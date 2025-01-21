from random import randint
from hashlib import sha256
from py_ecc.bls.hash_to_curve import hash_to_G1
from fields import Fq, Fq2, Fq12
from pairing import ate_pairing
from util import hash256, hash512
from bls12381 import q,a,b,gx,gy,g2x,g2y,n,h,h_eff, k, parameters
from ec import ( default_ec, default_ec_twist, bytes_to_point, 
                G1Infinity, G2Infinity, G1Generator,G2Generator,
                G1FromBytes, G2FromBytes, point_to_bytes,
                add_points, scalar_mult, y_for_x, AffinePoint)

class Node:
    def __init__(self, node_id, public_parameters, threshold, message):
        self.node_id                = node_id
        self.public_parameters      = public_parameters
        self.threshold              = threshold
        self.f_poly                 = None
        self.g_poly                 = None
        self.commitments            = None
        self.received_commitments   = {}
        self.received_shares        = {}
        self.vk                     = []
        self.sk                     = []
        self.partial_vk             = []
        self.partial_sk             = []
        self.rho                    = []
        self.point_exp_rho          = []
        self.partial_sk_prime       = []
        self.partial_vk_prime       = []
        self.indexed_message        = {}
        self.partial_signature      = []
        self.rand_partial_signature = []
        self.message                = message
        #setup the nodes 
        self.sample_polynomials()
        self.calculate_commitment()

    
    def sample_polynomials(self):
        # polynomials represented in increasing order
        # i.e. f_poly[0] = f[0]
        self.f_poly = [randint(0, self.public_parameters['p'] - 1) for _ in range(self.threshold + 1)]
        self.g_poly = [randint(0, self.public_parameters['p'] - 1) for _ in range(self.threshold + 1)]

    def calculate_commitment(self):
        B = []
        C = []

        for i in range(len(self.f_poly)):
            B.append(scalar_mult(self.f_poly[i], self.public_parameters['g2'], default_ec_twist, Fq2))
            assert B[i].is_on_curve()
            C.append(scalar_mult(self.g_poly[i], self.public_parameters['g2'], default_ec_twist, Fq2))
            assert C[i].is_on_curve()
        
        self.commitments = {
            "B" : B,
            "C" : C
        }
    
    def calculate_commitment_sum(self, commitment):
        sum_B = G2Infinity().to_affine()
        sum_C = G2Infinity().to_affine()

        B = commitment['B']
        C = commitment['C']

        for l in range(len(B)):
                addend = scalar_mult(((self.node_id)**l), B[l], default_ec_twist, Fq2)
                sum_B  = add_points(sum_B, addend, default_ec_twist, Fq2)
        
        for l in range(len(C)):
                addend = scalar_mult(((self.node_id)**l), C[l], default_ec_twist, Fq2)
                sum_C  = add_points(sum_C, addend, default_ec_twist, Fq2)
        return sum_B, sum_C

    def eval_poly(self, poly_coefficients, var):
        """
        Evaluate the polynomial f(x) = a0 + a1*x + a2*x^2 + ... + an*x^n
        at x = `var`, where the constant term (a0) is added directly without
        being multiplied by `var` and coeffiecents of polynomial represented
        in increasing order
        """
        total = 0
        p = self.public_parameters['p']

        for power, coeff in enumerate(poly_coefficients):
            if power == 0:
                # Add the constant term directly
                total = (total + coeff) % p
            else:
                # Add the term with the variable (coeff * var^power) mod p
                total = (total + coeff * pow(var, power, p)) % p
    
        return total
    
    def share_values(self, receiver_id):

        f_val = self.eval_poly(self.f_poly, receiver_id)
        g_val = self.eval_poly(self.g_poly, receiver_id)
        shares = [f_val, g_val]

        return shares, self.commitments
    
    def receive_data(self, sender_id, receiver_id, share_value, commitment_value):
        """
        Store the data in this node's dictionaries.
        We explicitly keep track of both sender_id and receiver_id in the key.
        """
        key                            = (sender_id, receiver_id)
        self.received_shares[key]      = share_value
        self.received_commitments[key] = commitment_value
    
    def consistency_check(self):
        compaints = []
        for (sender_id, receiver_id) in self.received_shares:
            
            share_val  = self.received_shares[(sender_id, receiver_id)]
            lhs_B = scalar_mult(share_val[0], self.public_parameters['g2'], default_ec_twist, Fq2)
            lhs_C = scalar_mult(share_val[1], self.public_parameters['g2'], default_ec_twist, Fq2)

            commitment = self.received_commitments[(sender_id, receiver_id)]
            sum_B, sum_C = self.calculate_commitment_sum(commitment)
            
            result = isEqual(lhs_B, sum_B) and isEqual(lhs_C, sum_C)
            if(result != True):
               print("Non consistent share, a complaint will be issued.")
               compaints.append(sender_id)
        print("chech ended")
        return compaints   
    
    def calculate_partial_keys(self):
        partial_key_x = 0
        partial_key_y = 0

        for share in self.received_shares.values():
            partial_key_x += share[0]
            partial_key_y += share[1]
        self.partial_sk = [partial_key_x % self.public_parameters['p'], partial_key_y % self.public_parameters['p']]

        sum_B = G2Infinity().to_affine()
        sum_C = G2Infinity().to_affine()
        for commitment in self.received_commitments.values():
            sum_Bj, sum_Cj = self.calculate_commitment_sum(commitment)
            sum_B += sum_Bj
            sum_C += sum_Cj
        self.partial_vk = [sum_B, sum_C]
        return
    
    def rand_sk_share(self):
        self.partial_sk_prime.append(self.partial_sk[0] + self.rho[0])
        self.partial_sk_prime.append(self.partial_sk[1] + self.rho[1])
        return
    
    def rand_pk_share(self):
        self.partial_vk_prime.append(add_points(self.partial_vk[0], self.point_exp_rho[0], default_ec_twist, Fq2))
        self.partial_vk_prime.append(add_points(self.partial_vk[1], self.point_exp_rho[1], default_ec_twist, Fq2))
        return
    
    def hash_string_to_G1(self, node_id) -> AffinePoint:
        result = G1Generator()
        #using hash-to-curve from py_ecc library
        #cipher_suit for hash-to-curve
        DST_G1 = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_"
        node_id_str = bytearray(node_id)
        id_converted_point = hash_to_G1(node_id_str, DST_G1, sha256)
        id_converted_point_x = id_converted_point[0] / id_converted_point[2] 
        id_converted_point_y = id_converted_point[1] / id_converted_point[2]

        #convert the result from py_ecc library
        fq_point_x = Fq(q, int(id_converted_point_x))
        fq_point_y = Fq(q, int(id_converted_point_y))
        result_affine_point = AffinePoint(fq_point_x, fq_point_y, False, ec=default_ec)
        result_is_on_curve = result_affine_point.is_on_curve()
        if(result_is_on_curve == True):
            result = result_affine_point   
        return result
    
    def indexed_message_encoding(self):
        h = self.hash_string_to_G1(self.node_id)

        #convert message to integer
        m  = int.from_bytes((hash256(self.message) + hash256(self.message)[16:]), byteorder="big")
        M1 = scalar_mult(m, h, default_ec, Fq)
        M2 = scalar_mult(m, self.public_parameters['g2'], default_ec_twist, Fq2)
        
        self.indexed_message = {
            "node_id" : self.node_id,
            "h" : h,
            "M1" : M1,
            "M2" : M2
        }

        return
    
    def partial_sign_gen(self, public_parameters, partial_secret_key, indexed_message):
        sigma = []
        #check consistency
        h  = indexed_message['h']
        M1 = indexed_message['M1']
        M2 = indexed_message['M2']
        lhs = ate_pairing(h.to_jacobian(), M2.to_jacobian(), default_ec)
        rhs = ate_pairing(M1.to_jacobian(), public_parameters['g2'].to_jacobian(), default_ec)
        if lhs != rhs:
            #abort
            print(f"PSignKen has failed.")
        
        first_addend  = scalar_mult(partial_secret_key[0], h, default_ec, Fq)
        second_addend = scalar_mult(partial_secret_key[1], M1, default_ec, Fq)
        addition_result = add_points(first_addend, second_addend, default_ec, Fq)

        sigma.append(h)
        sigma.append(addition_result)

        self.partial_signature = sigma
        return

    def adapt(self, public_parameters, indexed_message, partial_signature, randomizer, partial_secret_key):
        #TODO do we need all parameters except rho and sk_i'
        self.rand_partial_signature.append(partial_signature[0])

        h    = indexed_message['h']
        M1   = indexed_message['M1']
        tmp1 = scalar_mult(partial_secret_key[0], h, default_ec, Fq)
        tmp2 = scalar_mult(partial_secret_key[1], M1, default_ec, Fq)
        tmp = add_points(tmp1, tmp2, default_ec, Fq)
        self.rand_partial_signature.append(tmp)

        return

    def partial_sign_verify(self, public_parameters, partial_verification_key, M1, M2, rand_partial_signature):
        h = rand_partial_signature[0]
        s = rand_partial_signature[1]

        res1 = isEqual(h, G1Infinity().to_affine())
        res2 = isEqual(M1, G1Infinity().to_affine())
        res3 = ate_pairing(h.to_jacobian() , M2.to_jacobian(), default_ec) == \
               ate_pairing(M1.to_jacobian(), public_parameters['g2'].to_jacobian(), default_ec)
        res4 = add_points(ate_pairing(h.to_jacobian(), partial_verification_key[0].to_jacobian(), default_ec),\
                          ate_pairing(M1.to_jacobian(), partial_verification_key[1].to_jacobian(), default_ec),\
                          default_ec, Fq12) == ate_pairing(s.to_jacobian(), public_parameters['g2'].to_jacobian(), default_ec)
        
        if res1 and res2 and res3 and res4:
            return True
        else:
            return False

def distribute_shares(nodes):
    """
    Simulate sending and receiving shares among all nodes.
    Each node i sends share_values(i->j) to node j.
    """
    
    for sender in nodes:
        for receiver in nodes:
                #nodelar kendilerine de share hesaplayacak
                share_val, commit_val = sender.share_values(receiver.node_id)
                receiver.receive_data(sender.node_id, receiver.node_id, share_val, commit_val)

def setup(total_participant, threshold, message):
    #generators
    g1 = G1Generator(default_ec).to_affine()
    g2 = G2Generator(default_ec_twist).to_affine()
    public_parameters = {
            "g1" : g1,
            "g2" : g2,
            "q" : q,
            "p" : n
        }
    #init Nodes
    nodes = [Node(i, public_parameters, threshold, message) for i in range(1, total_participant + 1)]
    return nodes, public_parameters

def isEqual(pointA, pointB)-> bool:
        if not isinstance(pointA, AffinePoint):
            return False
        if not isinstance(pointB, AffinePoint):
            return False
        return (
            pointA.x == pointB.x and pointA.y == pointB.y and pointA.infinity == pointB.infinity
        )

def issue_complaints(complaints, complaint_list):
    for node_id in complaint_list:
        if node_id in complaints:
            complaints[node_id] += 1
        else:
            print(f"Warning: Node ID {node_id} not found in the compaints dictionary.")

# Function to remove nodes based on complaint threshold
def remove_nodes_above_threshold(nodes, complaints, threshold):
    """
    Remove nodes from the list if the number of complaints against their node_id exceeds the threshold.
    :param nodes: List of Node instances.
    :param complaints: Dictionary of complaints.
    :param threshold: Maximum allowed complaints before removal.
    :return: Updated list of nodes.
    """
    return [node for node in nodes if complaints.get(node.node_id, 0) <= threshold]

def calculate_global_verification_key(nodes, public_parameters):
    """
    Calculate the global keys vk_00 and vk_01 by summing the f_poly[0] and g_poly[0] values of all nodes.
    :param nodes: List of Node instances.
    :return: A list [vk_00, vk_01] where:
             vk_00 is the sum of all node.f_poly[0],
             vk_01 is the sum of all node.g_poly[0].
    """
    sk_0 = sum(node.f_poly[0] for node in nodes if node.f_poly)
    sk_1 = sum(node.g_poly[0] for node in nodes if node.g_poly)
    vk_00 = scalar_mult(sk_0, public_parameters['g2'], default_ec_twist, Fq2)
    vk_01 = scalar_mult(sk_1, public_parameters['g2'], default_ec_twist, Fq2)
    #do we need sk ? clarifiy TODO
    vk = [vk_00, vk_01]
    return vk

def rand_gen(nodes, public_parameters):
    r_x  = 0
    r_y  = 0
    p_rx = 0
    p_ry = 0
    for node in nodes:
        r_x = randint(0, public_parameters['p'] - 1)
        r_y = randint(0, public_parameters['p'] - 1)
        p_rx = scalar_mult(r_x, public_parameters['g2'], default_ec_twist, Fq2)
        p_ry = scalar_mult(r_y, public_parameters['g2'], default_ec_twist, Fq2)
        node.rho = [r_x, r_y]
        node.point_exp_rho = [p_rx, p_ry]
    return

def rand_pk(public_parameters, vk, rho):
    vk_prime = []
    point_exp_rho = []
    point_exp_rho.append(scalar_mult(rho[0], public_parameters['g2'], default_ec_twist, Fq2))
    point_exp_rho.append(scalar_mult(rho[1], public_parameters['g2'], default_ec_twist, Fq2))
    vk_prime.append(add_points(vk[0], point_exp_rho[0], default_ec_twist, Fq2))
    vk_prime.append(add_points(vk[1], point_exp_rho[1], default_ec_twist, Fq2))

    return vk_prime

def key_gen(nodes, public_parameters, total_participant, threshold):
    
    complaints = {node_id: 0 for node_id in range(1, total_participant + 1)}

    distribute_shares(nodes)

    for node in nodes:
        complaint_list = node.consistency_check()

    issue_complaints(complaints, complaint_list)
    # If complaints against node_id > t, disqualify the node
    nodes = remove_nodes_above_threshold(nodes, complaints, threshold)
    for node in nodes:
        node.qualified_node_count = len(nodes)

    global_vk = calculate_global_verification_key(nodes, public_parameters)
    sk = []
    vk = []
    for node in nodes:
        node.calculate_partial_keys()
        sk.append(node.partial_sk)
        vk.append(node.partial_vk)
    
    rand_gen(nodes, public_parameters)

    return sk, vk, global_vk


if __name__ == "__main__":
    
    security_param    = 128  # Security parameter
    total_participant = 3  # Number of participants, n
    threshold         = 2  # Threshold t
    message           = b'Hello World'

    nodes, public_parameters = setup(total_participant, threshold, message)
    sk, vk, global_vk        = key_gen(nodes, public_parameters, total_participant, threshold)
    for node in nodes:
        node.rand_sk_share()
        node.rand_pk_share()
        node.indexed_message_encoding()
        node.partial_sign_gen(node.public_parameters, node.partial_sk, node.indexed_message)
        node.adapt(node.public_parameters, node.indexed_message, node.partial_signature, node.rho , node.partial_sk)
        node.partial_sign_verify(node.public_parameters, node.partial_vk_prime, node.indexed_message['M1'],\
                                node.indexed_message['M2'], node.rand_partial_signature)

    
    #TODO what would be the calculation of rho
    rho =[0, 0]
    vk_prime = rand_pk(public_parameters, global_vk, rho)


3
print("Protocol Ends Here")







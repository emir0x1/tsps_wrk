from random import randint
from fields import Fq, Fq2, Fq12
from pairing import ate_pairing
from util import hash256, hash512
from bls12381 import q,a,b,gx,gy,g2x,g2y,n,h,h_eff, k, parameters
from ec import ( default_ec, default_ec_twist, bytes_to_point, 
                G2Infinity, G1Generator,G2Generator,scalar_mult_jacobian,
                G1FromBytes, G2FromBytes, point_to_bytes,
                add_points_jacobian,y_for_x, JacobianPoint)

class Node:
    def __init__(self, node_id, pp, threshold):
        self.node_id              = node_id
        self.pp                   = pp
        self.threshold            = threshold
        self.f_poly               = None
        self.g_poly               = None
        self.commitments          = None
        self.received_commitments = {}
        self.received_shares      = {}
    
    def pedDKG(self):
        return 0
    
    def sample_polynomials(self):
        #TODO randint sifirdan baslat
        self.f_poly = [randint(1, self.pp['p'] - 1) for _ in range(self.threshold + 1)]
        self.g_poly = [randint(1, self.pp['p'] - 1) for _ in range(self.threshold + 1)]

    def calculate_commitment(self):
        B = []
        C = []

        reversed_coeffs = self.f_poly[::-1]
        for i in range(len(self.f_poly)):
            B.append(scalar_mult_jacobian(reversed_coeffs[i], self.pp['g2'], default_ec_twist, Fq2))
            C.append(scalar_mult_jacobian(reversed_coeffs[i], self.pp['g2'], default_ec_twist, Fq2))
        
        self.commitments = {
            "B" : B,
            "C" : C
        }

    def eval_poly_f(self, var):
        total = 0
        for power, coeff in enumerate(self.f_poly):
            total += (coeff * (var ** power)) % self.pp['p']
        return total
    
    def eval_poly_g(self, var):
        total = 0
        for power, coeff in enumerate(self.g_poly):
            total += (coeff * (var ** power)) % self.pp['p']
        return total
    
    def share_values(self, receiver_id):
        self.sample_polynomials()

        f_val = self.eval_poly_f(receiver_id)
        g_val = self.eval_poly_g(receiver_id)
        shares = [f_val, g_val]

        self.calculate_commitment()

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
        for (sender_id, receiver_id) in self.received_shares:
            share_val  = self.received_shares[(sender_id, receiver_id)]
            commit_val = self.received_commitments[(sender_id, receiver_id)]
            
            B = commit_val['B']
            C = commit_val['C']

            lhs_f = scalar_mult_jacobian(share_val[0], self.pp['g2'], default_ec_twist, Fq2)
            print( lhs_f)
            rhs_f = G2Infinity()
            for i in range(len(B)):
                rhs_f = add_points_jacobian(rhs_f, scalar_mult_jacobian(((self.node_id)**i), B[i], default_ec_twist, Fq2))
            
            print( rhs_f)
            result = isEqual(lhs_f, rhs_f)
            if(result != True):
               print("Non consistent share, a complaint will be issued.")
            
        print("chech ended")

def distribute_shares(nodes):
    """
    Simulate sending and receiving shares among all nodes.
    Each node i sends share_values(i->j) to node j.
    """
    
    for sender in nodes:
        for receiver in nodes:
            if sender.node_id != receiver.node_id:
                #nodelar kendilerine de share hesaplayacak TODO
                share_val, commit_val = sender.share_values(receiver.node_id)
                receiver.receive_data(sender.node_id, receiver.node_id, share_val, commit_val)

def setup(total_participant, threshold):
    #generators
    g1 = G1Generator(default_ec)
    g2 = G2Generator(default_ec_twist)
    pp = {
            "g1" : g1,
            "g2" : g2,
            "q" : q,
            "p" : n
        }
    #init Nodes
    nodes = [Node(i, pp, threshold) for i in range(1, total_participant + 1)]
    return nodes

def isEqual(pointA, pointB)-> bool:
        if not isinstance(pointA, JacobianPoint):
            return False
        if not isinstance(pointB, JacobianPoint):
            return False
        return (
            pointA.x == pointB.x and pointA.y == pointB.y and pointA.infinity == pointB.infinity
        )

if __name__ == "__main__":
    
    security_param    = 128  # Security parameter
    total_participant = 3  # Number of participants
    threshold         = 2  # Threshold
    nodes             = setup(total_participant, threshold)

    distribute_shares(nodes)

    for node in nodes:
        node.consistency_check()

        




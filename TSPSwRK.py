from random import randint, sample
from hashlib import sha256
from py_ecc.bls.hash_to_curve import hash_to_G1
from fields import Fq, Fq2, Fq12
from pairing import ate_pairing
from util import hash256, hash512
from bls12381 import q,a,b,gx,gy,g2x,g2y,n,h,h_eff,k, parameters
from ec import ( default_ec, default_ec_twist, bytes_to_point,
                G1Infinity, G2Infinity, G1Generator,G2Generator, 
                G1FromBytes, G2FromBytes, point_to_bytes,
                add_points, scalar_mult, AffinePoint)


##############################################################################
# Helper functions
##############################################################################

def isEqual(pointA, pointB)-> bool:
    """
    Checks exact equality of two AffinePoint objects in G1 or G2.
    """
    if not isinstance(pointA, AffinePoint):
        return False
    if not isinstance(pointB, AffinePoint):
        return False
    return (
        pointA.x == pointB.x and pointA.y == pointB.y and pointA.infinity == pointB.infinity
    )

def add_points_ec(a, b, ec_curve, field_mod):
    return add_points(a, b, ec_curve, field_mod)

def get_lagrange_coefficient(idx, subset_ids, p):
    """
    Standard Lagrange coefficient for index `idx` among subset of node IDs `subset_ids`.
    ℓ_idx(0) = ∏_{j ∈ subset_ids, j != idx} (−j)/(idx−j) (mod p).
    """
    numerator = 1
    denominator = 1
    for j in subset_ids:
        if j == idx:
            continue
        numerator = (numerator * (-j % p)) % p
        denominator = (denominator * ((idx - j) % p)) % p
    denom_inv = pow(denominator, p - 2, p)
    return (numerator * denom_inv) % p


##############################################################################
# Node class
##############################################################################

class Node:
    def __init__(self, node_id, public_parameters, threshold, message, index):
        self.node_id                   = node_id
        self.public_parameters         = public_parameters
        self.threshold                 = threshold

        self.f_poly                    = None
        self.g_poly                    = None
        self.commitments               = None
        self.received_commitments      = {}
        self.received_commitments_rand = {}
        self.received_shares           = {}
        self.received_shares_rand      = {}
        

        self.randomizer                = []
        self.randomizer_x              = None
        self.randomizer_y              = None
        self.partial_rand              = [] # (r_i0, r_i1)
        self.partial_rand_pt           = [] # (g2^{r_i0}, g2^{r_i0})
 
        self.partial_secret_key        = []   # (x_i, y_i)
        self.partial_ver_key           = []   # (g2^{x_i}, g2^{y_i})
 
        self.partial_secret_key_prime  = []   # (x_i + r0, y_i + r1)
        self.partial_ver_key_prime     = []   # (g2^{x_i + r0}, g2^{y_i + r1})
 
        self.partial_signature         = []   # (h, s_i)
        self.rand_partial_signature    = []   # (h, s'_i)
 
        self.message                   = message
        self.index                     = index


    def sample_polynomials(self):
        p = self.public_parameters['p']
        # Each polynomial has length = threshold => degree = threshold - 1
        first_poly = [randint(0, p - 1) for _ in range(self.threshold)]
        second_poly = [randint(0, p - 1) for _ in range(self.threshold)]
        return first_poly, second_poly


    def eval_poly(self, poly_coefficients, var):
        """
        Evaluate polynomial sum_{i=0}^{t-1} poly[i] * var^i (mod p).
        """
        p = self.public_parameters['p']
        total = 0
        for power, coeff in enumerate(poly_coefficients):
            total = (total + coeff * pow(var, power, p)) % p
        return total

    def calculate_commitment(self, first_poly, second_poly):
        """
        For each coefficient in f_poly, g_poly, commit in G2.
        """
        B = []
        C = []
        ec_twist = default_ec_twist
        field_mod = Fq2
        for i in range(len(first_poly)):  # which is `threshold`
            B_i = scalar_mult(first_poly[i], self.public_parameters['g2'], ec_twist, field_mod)
            C_i = scalar_mult(second_poly[i], self.public_parameters['g2'], ec_twist, field_mod)
            B.append(B_i)
            C.append(C_i)
        commitments = {"B": B, "C": C}
        return commitments

    def calculate_commitment_sum(self, commitment):
        """
        sum_{l} (node_id^l * B[l]), sum_{l} (node_id^l * C[l]) in G2
        """
        sum_B = G2Infinity().to_affine()
        sum_C = G2Infinity().to_affine()
        ec_twist = default_ec_twist
        field_mod = Fq2

        B = commitment['B']
        C = commitment['C']
        for l in range(len(B)):
            addend_B = scalar_mult(pow(self.node_id, l), B[l], ec_twist, field_mod)
            sum_B    = add_points_ec(sum_B, addend_B, ec_twist, field_mod)
        for l in range(len(C)):
            addend_C = scalar_mult(pow(self.node_id, l), C[l], ec_twist, field_mod)
            sum_C    = add_points_ec(sum_C, addend_C, ec_twist, field_mod)

        return sum_B, sum_C

    def share_values(self, receiver_id, isRand):
        """
        Evaluate polynomials f, g at `receiver_id`. Return (f(receiver_id), g(receiver_id)).
        """
        if not isRand:
            first_val  = self.eval_poly(self.f_poly, receiver_id)
            second_val = self.eval_poly(self.g_poly, receiver_id)
            commit_val = self.commitments
        else:
            first_val = self.eval_poly(self.randomizer_x, receiver_id)
            second_val = self.eval_poly(self.randomizer_y, receiver_id)
            commit_val = self.randomizer
        return [first_val, second_val], commit_val

    def receive_data(self, sender_id, receiver_id, share_value, commitment_value, isRand):
        key = (sender_id, receiver_id)
        if not isRand:
            self.received_shares[key] = share_value
            self.received_commitments[key] = commitment_value
        else:
            self.received_shares_rand[key]      = share_value
            self.received_commitments_rand[key] = commitment_value

    def consistency_check(self, isRand):
        """
        Check g2^{f_val} = polynomialCommitment for each share.
        If mismatch => complaint.
        """
        complaints = []
        ec_twist = default_ec_twist
        field_mod = Fq2
        
        if not isRand:
            received_shares      = self.received_shares
            received_commitments = self.received_commitments
        else:
            received_shares      = self.received_shares_rand
            received_commitments = self.received_commitments_rand

        for (sender_id, receiver_id) in received_shares:
            share_val = received_shares[(sender_id, receiver_id)]
            f_val, g_val = share_val
            lhs_B = scalar_mult(f_val, self.public_parameters['g2'], ec_twist, field_mod)
            lhs_C = scalar_mult(g_val, self.public_parameters['g2'], ec_twist, field_mod)

            commitment   = received_commitments[(sender_id, receiver_id)]
            sum_B, sum_C = self.calculate_commitment_sum(commitment)

            if not (isEqual(lhs_B, sum_B) and isEqual(lhs_C, sum_C)):
                print(f"Node {self.node_id}: Inconsistent share from {sender_id}")
                complaints.append(sender_id)
        return complaints

    def calculate_partial_keys(self, isRand):
        """
        sum_{all senders} f_val => x_i, sum_{all senders} g_val => y_i
        partial_ver_key = sums of commitments
        """
        p = self.public_parameters['p']
        ec_twist = default_ec_twist
        field_mod = Fq2

        if not isRand:
            received_shares      = self.received_shares
            received_commitments = self.received_commitments
        else:
            received_shares      = self.received_shares_rand
            received_commitments = self.received_commitments_rand

        x_i = 0
        y_i = 0
        for share_val in received_shares.values():
            x_i = (x_i + share_val[0]) % p
            y_i = (y_i + share_val[1]) % p
        partial_result_val = [x_i, y_i]

        sum_B = G2Infinity().to_affine()
        sum_C = G2Infinity().to_affine()
        for commitment in received_commitments.values():
            sb, sc = self.calculate_commitment_sum(commitment)
            sum_B  = add_points_ec(sum_B, sb, ec_twist, field_mod)
            sum_C  = add_points_ec(sum_C, sc, ec_twist, field_mod)
        partial_result_pt = [sum_B, sum_C]

        if not isRand:
            self.partial_secret_key = partial_result_val
            self.partial_ver_key    = partial_result_pt
        else:
            self.partial_rand    = partial_result_val
            self.partial_rand_pt = partial_result_pt
        return

    ########################################################################
    # Randomizing partial key: single (r_0, r_1) for all nodes
    ########################################################################

    def rand_secret_key_share(self):
        """
        partial_secret_key_prime = (x_i + r_0, y_i + r_1)
        """
        p = self.public_parameters['p']
        x_prime = (self.partial_secret_key[0] + self.partial_rand[0]) % p
        y_prime = (self.partial_secret_key[1] + self.partial_rand[1]) % p
        self.partial_secret_key_prime = [x_prime, y_prime]

    def rand_public_key_share(self):
        """
        partial_ver_key_prime = ( g2^{x_i} * g2^{r_0}, g2^{y_i} * g2^{r_1} )
        """
        ec_twist = default_ec_twist
        field_mod = Fq2

        # original partial VK = (vk_i0, vk_i1)
        vk_i0 = self.partial_ver_key[0]
        vk_i1 = self.partial_ver_key[1]

        vk0_prime = add_points_ec(self.partial_ver_key[0], self.partial_rand_pt[0], ec_twist, field_mod)
        vk1_prime = add_points_ec(self.partial_ver_key[1], self.partial_rand_pt[1], ec_twist, field_mod)

        self.partial_ver_key_prime = [vk0_prime, vk1_prime]

    ########################################################################
    # Partial Sign & Adapt
    ########################################################################

    def partial_sign_gen(self, indexed_message):
        """
        sigma_i = (h, h^{x_i} * M1^{y_i})
        """
        ec = default_ec
        field_mod = Fq
        h  = indexed_message['h']
        M1 = indexed_message['M1']
        M2 = indexed_message['M2']

        # iDH check
        lhs = ate_pairing(h.to_jacobian(), M2.to_jacobian(), ec)
        rhs = ate_pairing(M1.to_jacobian(), self.public_parameters['g2'].to_jacobian(), ec)
        if lhs != rhs:
            print(f"Node {self.node_id} partial_sign_gen fails iDH check.")
            self.partial_signature = []
            return

        x_i = self.partial_secret_key[0]
        y_i = self.partial_secret_key[1]
        p1  = scalar_mult(x_i, h, ec, field_mod)
        p2  = scalar_mult(y_i, M1, ec, field_mod)
        s_i = add_points_ec(p1, p2, ec, field_mod)

        self.partial_signature = [h, s_i]

    def adapt(self, indexed_message):
        """
        sigma'_i = (h, h^{x_i + r_0} * M1^{y_i + r_1})
        """
        if len(self.partial_signature) < 2:
            return
        ec = default_ec
        field_mod = Fq
        h  = indexed_message['h']
        M1 = indexed_message['M1']

        x_prime = self.partial_secret_key_prime[0]
        y_prime = self.partial_secret_key_prime[1]

        part1 = scalar_mult(x_prime, h, ec, field_mod)
        part2 = scalar_mult(y_prime, M1, ec, field_mod)
        s_adapted = add_points_ec(part1, part2, ec, field_mod)

        self.rand_partial_signature = [h, s_adapted]

    def partial_sign_verify(self, indexed_message):
        """
        Check e(h, M2) = e(M1, g2) and e(h, vk'_i0)* e(M1,vk'_i1) = e(rand_partial_signature[1], g2)
        """
        if len(self.rand_partial_signature) < 2:
            print(f"Node {self.node_id} partial_sign_verify fails: no signature.")
            return False

        ec = default_ec
        h, s_prime = self.rand_partial_signature
        M1 = indexed_message['M1']
        M2 = indexed_message['M2']

        if h == G1Infinity().to_affine():
            print(f"Node {self.node_id} partial_sign_verify fails iDH check.")
            return False
        
        if M1 == G1Infinity().to_affine():
            print(f"Node {self.node_id} partial_sign_verify fails iDH check.")
            return False

        # 1) iDH check
        lhs_1 = ate_pairing(h.to_jacobian(), M2.to_jacobian(), ec)
        rhs_1 = ate_pairing(M1.to_jacobian(), self.public_parameters['g2'].to_jacobian(), ec)
        if lhs_1 != rhs_1:
            print(f"Node {self.node_id} partial_sign_verify fails iDH check.")
            return False

        # 2) e(h, vk'_{i0}) * e(M1, vk'_{i1}) == e(s_prime, g2)
        lhs_2_1 = ate_pairing(h.to_jacobian(), self.partial_ver_key_prime[0].to_jacobian(), ec)
        lhs_2_2 = ate_pairing(M1.to_jacobian(), self.partial_ver_key_prime[1].to_jacobian(), ec)
        lhs_2   = lhs_2_1.__mul__(lhs_2_2)
        rhs_2   = ate_pairing(s_prime.to_jacobian(), self.public_parameters['g2'].to_jacobian(), ec)
        if lhs_2 != rhs_2:
            print(f"Node {self.node_id} partial_sign_verify fails final pairing mismatch.")
            return False

        return True

def test_randomizer(nodes, threshold, p):
    """
    Demonstrate that any subset of size `threshold` can reconstruct the same
    global randomizer (X, Y) via Lagrange interpolation of the global polynomials' shares.
    """
    # 1) The true global randomizer from summing polynomials
    global_rand = get_global_randomizer(nodes)
    print(f"[TEST] Global randomizer (expected) = {global_rand}")

    # 2) Build the "global polynomials" by summing node randomizers
    length = threshold
    all_x = [node.randomizer_x for node in nodes]
    all_y = [node.randomizer_y for node in nodes]
    Gx = sum_polynomials(all_x, length, p)
    Gy = sum_polynomials(all_y, length, p)

    # 3) Each node i's share = (i, Gx(i)), (i, Gy(i))
    node_shares_x = [(node.node_id, eval_polynomial(Gx, node.node_id, p)) for node in nodes]
    node_shares_y = [(node.node_id, eval_polynomial(Gy, node.node_id, p)) for node in nodes]

    # 4) Pick a few subsets of size `threshold` and reconstruct
    import itertools
    subsets = list(itertools.combinations(nodes, threshold))
    # limit to e.g. 5 for brevity
    subsets = subsets[:5]

    for s in subsets:
        subset_ids = [n.node_id for n in s]
        sx = [(i, val) for (i, val) in node_shares_x if i in subset_ids]
        sy = [(i, val) for (i, val) in node_shares_y if i in subset_ids]
        # reconstruct
        X_recon = lagrange_interpolate_zero(sx, p)
        Y_recon = lagrange_interpolate_zero(sy, p)
        print(f"  Subset {subset_ids} => reconstructed randomizer = ({X_recon}, {Y_recon})")

    print("Done testing randomizer.\n")


##############################################################################
# Distribute main key shares
##############################################################################

def distribute_shares(nodes, isRand=False):
    for sender in nodes:
        for receiver in nodes:
            share_val, commit_val = sender.share_values(receiver.node_id, isRand)
            receiver.receive_data(sender.node_id, receiver.node_id, share_val, commit_val, isRand)

def remove_nodes_above_threshold(nodes, complaints, threshold):
    return [node for node in nodes if complaints.get(node.node_id, 0) <= threshold]

def issue_complaints(complaints, c_list):
    for node_id in c_list:
        complaints[node_id] = complaints.get(node_id, 0) + 1

def calculate_global_verification_key(nodes, public_parameters, isRand):
    """
    Summation of f_poly[0] => x, g_poly[0] => y,
    then vk = (g2^x, g2^y)
    """
    p = public_parameters['p']
    x_agg = 0
    y_agg = 0

    for node in nodes:
        x_agg = (x_agg + (node.f_poly[0] if not isRand else node.randomizer_x[0])) % p
        y_agg = (y_agg + (node.g_poly[0] if not isRand else node.randomizer_y[0])) % p
    ec_twist = default_ec_twist
    field_mod = Fq2
    vk0 = scalar_mult(x_agg, public_parameters['g2'], ec_twist, field_mod)
    vk1 = scalar_mult(y_agg, public_parameters['g2'], ec_twist, field_mod)
    return [vk0, vk1]

def key_gen(nodes, public_parameters, threshold, isRand=False):
    """
    1) Distribute shares
    2) Consistency checks
    3) Drop any node with too many complaints
    4) Each node sums up its shares => partial (x_i, y_i)
    5) global_ver_key = (g2^{x}, g2^{y})
    """
    complaints = {nid:0 for nid in range(1, len(nodes)+1)}
    for node in nodes:
        first_poly, second_poly = node.sample_polynomials()
        commitments = node.calculate_commitment(first_poly, second_poly)
        if not isRand:
            node.f_poly = first_poly
            node.g_poly = second_poly
            node.commitments = commitments
        else:
            node.randomizer_x = first_poly
            node.randomizer_y = second_poly
            node.randomizer = commitments

    distribute_shares(nodes, isRand)

    for node in nodes:
        c_list = node.consistency_check(isRand)
        issue_complaints(complaints, c_list)

    nodes_ok = remove_nodes_above_threshold(nodes, complaints, threshold)

    for node in nodes_ok:
        node.calculate_partial_keys(isRand)

    global_vk = calculate_global_verification_key(nodes_ok, public_parameters, isRand)
    return nodes_ok, global_vk


##############################################################################
# Randomizer for All Nodes
##############################################################################

def rand_gen(nodes, ppublic_parameters, threshold):
    """
    Each node generates random polynomials randomizer_x, randomizer_y
    of degree threshold-1. Called by each node.
    """
    isRand = True
    nodes, global_randomizer = key_gen(nodes, public_parameters, threshold, isRand)

    return nodes

def rand_pk(global_ver_key, r_0, r_1, public_parameters):
    """
    vk' = ( g2^{x} * g2^{r_0},  g2^{y} * g2^{r_1} )
    """
    ec_twist = default_ec_twist
    field_mod = Fq2
    vk0, vk1 = global_ver_key[0], global_ver_key[1]

    add_r0 = scalar_mult(r_0, public_parameters['g2'], ec_twist, field_mod)
    add_r1 = scalar_mult(r_1, public_parameters['g2'], ec_twist, field_mod)

    vk0_prime = add_points_ec(vk0, add_r0, ec_twist, field_mod)
    vk1_prime = add_points_ec(vk1, add_r1, ec_twist, field_mod)
    return [vk0_prime, vk1_prime]


##############################################################################
# Indexed Message / Hash-to-G1
##############################################################################

def hash_string_to_G1(i: int) -> AffinePoint:
    DST_G1 = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_"
    idx_bytes = i.to_bytes(4, 'big')
    pt3d = hash_to_G1(idx_bytes, DST_G1, sha256)
    x_coord = pt3d[0] / pt3d[2]
    y_coord = pt3d[1] / pt3d[2]
    fqx = Fq(q, int(x_coord))
    fqy = Fq(q, int(y_coord))
    aff_pt = AffinePoint(fqx, fqy, False, ec=default_ec)
    if not aff_pt.is_on_curve():
        raise ValueError("Hash-to-curve point not on curve.")
    return aff_pt

def indexed_message_encoding(public_parameters, message, index):
    """
    M1 = H(id)^m, M2 = g2^m, h = H(id).
    """
    h = hash_string_to_G1(index)
    full_hash = hash256(message) + hash256(message)[16:]
    m = int.from_bytes(full_hash, "big")

    ec = default_ec
    ec_twist = default_ec_twist
    field1 = Fq
    field2 = Fq2
    M1 = scalar_mult(m, h, ec, field1)
    M2 = scalar_mult(m, public_parameters['g2'], ec_twist, field2)
    return {
        "id": index,
        "h":  h,
        "M1": M1,
        "M2": M2
    }


##############################################################################
# DKG-style Randomizer Utilities
##############################################################################

def sum_polynomials(poly_list, length, p):
    """
    Given a list of polynomials (each is length `length`),
    return their sum mod p, also length `length`.
    """
    result = [0]*length
    for poly in poly_list:
        for i in range(length):
            result[i] = (result[i] + poly[i]) % p
    return result

def eval_polynomial(coeffs, x, p):
    """
    Evaluate polynomial with given coefficients at x mod p.
    coeffs[i] is the coefficient of x^i.
    """
    total = 0
    power = 1
    for c in coeffs:
        total = (total + c * power) % p
        power = (power * x) % p
    return total

def lagrange_interpolate_zero(shares, p):
    """
    Reconstruct f(0) from a list of (x_i, f(x_i)) using standard Lagrange interpolation mod p.
    """
    total = 0
    for i, (x_i, y_i) in enumerate(shares):
        numerator = 1
        denominator = 1
        for j, (x_j, _) in enumerate(shares):
            if j != i:
                numerator = (numerator * (-x_j % p)) % p
                denominator = (denominator * (x_i - x_j) % p) % p
        denom_inv = pow(denominator, p-2, p)
        term = (y_i * numerator) % p
        term = (term * denom_inv) % p
        total = (total + term) % p
    return total

def get_global_randomizer(subset_T):
    """
    Computes the "global" polynomials Gx, Gy by summing each node's randomizer_x, randomizer_y.
    Then the global secret randomizer = (Gx(0), Gy(0)).
    """
    if not subset_T:
        return None
    h = indexed_msg['h']
    ec = default_ec_twist
    field_mod = Fq2

    # 2) Aggregate using Lagrange interpolation w.r.t. node IDs
    r0_agg = 0
    r1_agg = 0
    subset_ids = [node.node_id for node in subset_T]
    for node in subset_T:
        r_i0, r_i1 = node.partial_rand
        lam_i = get_lagrange_coefficient(node.node_id, subset_ids, public_parameters['p'])
        contrib_r0 = (lam_i * r_i0) % public_parameters['p'] 
        contrib_r1 = (lam_i * r_i1) % public_parameters['p']
        r0_agg   = (r0_agg + contrib_r0) % public_parameters['p']
        r1_agg   = (r1_agg + contrib_r1) % public_parameters['p']

    return (r0_agg, r1_agg)



##############################################################################
# Reconstruct the final signature from subset T
##############################################################################

def reconst_signature(subset_T, public_parameters, indexed_msg):
    """
    sigma' = (h, ∑_{i in T} lambda_i * s'_i ).
    We use node IDs for Lagrange interpolation over partial signatures.
    """
    if not subset_T:
        return None
    h = indexed_msg['h']
    ec = default_ec
    field_mod = Fq

    # 1) Verify each partial signature from subset_T
    for node in subset_T:
        ok = node.partial_sign_verify(indexed_msg)
        if not ok:
            print(f"Node {node.node_id} partial signature verify fails.")
            return None

    # 2) Aggregate using Lagrange interpolation w.r.t. node IDs
    s_agg = G1Infinity().to_affine()
    subset_ids = [node.node_id for node in subset_T]
    for node in subset_T:
        h_i, s_i_prime = node.rand_partial_signature
        lam_i = get_lagrange_coefficient(node.node_id, subset_ids, public_parameters['p'])
        contrib = scalar_mult(lam_i, s_i_prime, ec, field_mod)
        s_agg   = add_points_ec(s_agg, contrib, ec, field_mod)

    return [h, s_agg]


def verify_signature(public_parameters, vk_prime, indexed_msg, signature):
    """
    Final check: e(h, M2) == e(M1, g2) and e(h, vk'_0)* e(M1, vk'_1) == e(s', g2)
    """
    if not signature or len(signature) < 2:
        return False
    h, s_agg = signature
    M1 = indexed_msg['M1']
    M2 = indexed_msg['M2']

    if h == G1Infinity().to_affine():
        return False
        
    if M1 == G1Infinity().to_affine():
        return False

    ec = default_ec

    # 3) iDH check
    lhs_1 = ate_pairing(h.to_jacobian(), M2.to_jacobian(), ec)
    rhs_1 = ate_pairing(M1.to_jacobian(), public_parameters['g2'].to_jacobian(), ec)
    if lhs_1 != rhs_1:
        return False

    # 4) final pairing check
    tmp1 = ate_pairing(h.to_jacobian(), vk_prime[0].to_jacobian(), ec)
    tmp2 = ate_pairing(M1.to_jacobian(), vk_prime[1].to_jacobian(), ec)
    lhs_2   = tmp1.__mul__(tmp2)
    rhs_2   = ate_pairing(s_agg.to_jacobian(), public_parameters['g2'].to_jacobian(), ec)
    return (lhs_2 == rhs_2)

def setup(total_participant, threshold, message):
    #generators
    g1 = G1Generator(default_ec).to_affine()
    g2 = G2Generator(default_ec_twist).to_affine()
    public_parameters = {
            "g1" : g1,
            "g2" : g2,
            "q" : q, 
            "p" : n # order og G1, G2 and GT
        }
    #init Nodes
    nodes = [Node(i, public_parameters, threshold, message, index) for i in range(1, total_participant + 1)]
    return nodes, public_parameters


##############################################################################
# MAIN
##############################################################################

if __name__ == "__main__":
    total_participant = 5
    threshold = 3

    message = b"Hello World"
    index   = len(message)

    # 1) Setup
    nodes, public_parameters = setup(total_participant, threshold, message)

    # Encode the message + index => (h, M1, M2)
    indexed_msg = indexed_message_encoding(public_parameters, message, index)

    # (B) Existing threshold BLS KeyGen for (x,y).
    nodes, global_vk = key_gen(nodes, public_parameters, threshold)

    if len(nodes) < threshold:
        print("Not enough valid nodes remain after complaints; aborting.")
        exit(1)

    # 3) RandGen (r_0, r_1)
    nodes = rand_gen(nodes, public_parameters, threshold)

    # ------------------------------------------------------------------------

    # 4) Each node randomizes partial key + partial VK
    for node in nodes:
        node.rand_secret_key_share()
        node.rand_public_key_share()

    # 5) Partial sign with original partial SK
    for node in nodes:
        node.partial_sign_gen(indexed_msg)

    # 6) Adapt partial signature with the single (r_0, r_1)
    for node in nodes:
        node.adapt(indexed_msg)

    # 7) Choose a subset T of size t
    subset_T = sample(nodes, k=threshold)
    
    # 8) Reconstruct final signature from subset T
    signature = reconst_signature(subset_T, public_parameters, indexed_msg)
    if not signature:
        print("Signature reconstruction failed.")
        exit(1)

    # 9) Randomize the *global* VK => vk' = (g2^{x+r_0}, g2^{y+r_1})
    global_rand = get_global_randomizer(subset_T)
    vk_prime = rand_pk(global_vk, global_rand[0], global_rand[1], public_parameters)

    # 10) Verify
    ok = verify_signature(public_parameters, vk_prime, indexed_msg, signature)
    if ok:
        print("✅  Signature verification PASSED.")
    else:
        print("❌  Signature verification FAILED.")

    print("Done.")

# SETUP

# Define the polynomial rings over the reals and rationals
R.<X> = PolynomialRing(RR, 'X')
Q.<X> = PolynomialRing(QQ, 'X') 

# Curve families
def MNT3():
    t = Q(6*X -1)
    q = Q(12*X^2 - 1)
    p = q + 1 - t
    return(t, p, q)

def MNT4():
    t = Q(-X)
    q = Q(X^2 + X + 1)
    p = q + 1 - t
    return(t, p, q)

def MNT6():
    t = Q(2*X + 1)
    q = Q(4*X^2 + 1)
    p = q + 1 - t
    return(t, p, q)

def Freeman():
    t = Q(10*X^2 + 5*X + 3)
    q = Q(25*X^4 + 25*X^3 + 25*X^2 + 10*X + 3)
    p = q + 1 - t
    return(t, p, q)

def BN():
    t = Q(6*X^2 + 1)
    q = Q(36*X^4 + 36*X^3 + 24*X^2 + 6*X + 1)
    p = q + 1 - t
    return(t, p, q)


# CANDIDATE EMBEDDING DEGREES

# INPUT: a parametrization of a family of pairing-friendly elliptic curves with prime order.
#        a bound K on the embedding degree to look for.
# OUTPUT: a list of potential embedding degrees k such that 3 <= k <= K and a curve from the
#         family *might* form a cycle with a curve with embedding degree k, along with conditions
#         on x mod k for each of these k.

def candidate_embedding_degrees(Family, K_low, K_high):
    
    (t, p, q) = Family()
    # Create an empty list to store the candidate embedding degrees
    embedding_degrees = []
    # Create an empty list to store the lists of modular conditions for each k
    modular_conditions = [None] * (K_high + 1)
    
    # Embedding degree k implies that q(x) = 1 (mod k). 
    # We check this condition in 0, ..., k-1 and build a list of candidates
    # such that any x has to be congruent to one of them modulo k.
    for k in range(K_low, K_high + 1):
        
        candidate = False
        
        for i in range(k):
            if ((q(i) % k) == 1):
                # First time a candidate k is discovered, add it to the list and 
                # create a list within modular_conditions to store the values i.
                if (not candidate):
                    candidate = True
                    embedding_degrees.append(k)
                    modular_conditions[k] = []
                modular_conditions[k].append(i)
            
    return embedding_degrees, modular_conditions


# AUXILIARY FUNCTIONS

def is_integer_valued(g):
    
    # Check if evaluation is integer in deg(g) + 1 consecutive points
    for x in range(g.degree()+1):
        if (not g(x) in ZZ):
            print(str(g) + " is not integer-valued.")
            return False
    return True

def find_relevant_root(w, b, side):
    
    # Decide whether to keep the left-most or right-most root
    i = -(1 + side) / 2
    
    # 0 <= w(x)
    C_1 = 0
    w_roots = R(w).roots()
    if (w_roots != []):
        C_1 = w_roots[i][0]
    # w(x) < b(x)
    C_2 = 0
    bw_roots = R(b - w).roots()
    if (bw_roots != []):
        C_2 = bw_roots[i][0]
              
    # return the relevant extremal root
    if (side == -1):
        return ceil(min(C_1, C_2))
    else:
        return floor(max(C_1, C_2))
    
def check_embedding_degree(px, qx, k):
    # Checks divisibility condition
    if ((px^k - 1) % qx != 0): return False
    # Checks that divisibility conditions does not happen for smaller exponents
    div = divisors(k)
    div.remove(k)
    for j in div:
        if ((px^j - 1) % qx == 0):
            return False
    return True


# COMPUTATION OF THE BOUNDS N_left, N_right

# INPUT: two integer-valued polynomials a, b in Q[X].
# OUTPUT: bounds N_left, N_right in Z, as described in Lemma 4.4.

def compute_bounds(a, b):
    
    # Check that b has even degree and positive leading coefficient
    if (b.degree() % 2 == 1 or b.leading_coefficient() < 0):
        print("Invalid divisor.")
        return
    
    # Check that a, b are integer valued.
    if (not is_integer_valued(a) or not is_integer_valued(b)):
        return
    
    # Polynomial division
    (h, r) = a.quo_rem(b)
    
    # Compute c so that ch, cr are in Z[X]
    denominators = [i.denominator() for i in (h.coefficients() + r.coefficients())]
    c = lcm(denominators)
    
    # Compute signs
    sigma_right = sign(r.leading_coefficient())
    sigma_left = sigma_right * (-1)^(r.degree())
    
    # We compute the polynomials w_left, w_right such that 
    # 0 <= w_left < b(x) for all x < N_left, and
    # 0 <= w_right < b(x) for all x > N_right.
    w_left = c * r + ((1 - sigma_left) / 2) * b
    w_right = c * r + ((1 - sigma_right) / 2) * b
    
    # Compute N_left, N_right
    N_left = find_relevant_root(w_left, b, -1)
    N_right = find_relevant_root(w_right, b, 1)
    
    return (N_left, N_right)


# EXHAUSTIVE SEARCH

# INPUT: a parametrization of a family of pairing-friendly elliptic curves with prime order.
#        an embedding degree k.
#        bounds N_left, N_right.
# OUTPUT: a list of integers x in [N_left, N_right] such that the curve parameterized by (t(x), p(x), q(x))
#         forms a cycle with a curve with embedding degree k.

def exhaustive_search(Family, k, N_left, N_right, mod_cond):
    
    (t, p, q) = Family()
    curves  = []
    
    for x in range(N_left, N_right+1):
        # We skip those values that will never yield q(x) = 1 (mod k), as precomputed above.
        if (not (x % k) in mod_cond): continue
        # Check the embedding degree condition 
        if (check_embedding_degree(p(x), q(x), k)):
            curves.append((x, k, t(x), p(x), q(x)))
    
    return curves


# MAIN FUNCTION

# INPUT: a parameterization of a family of pairing-friendly ellipitc curves with prime order.
#        a bound K on the embedding degree to look for
# OUTPUT: all the cycles involving a curve from the family and a prime-order curve with embedding degree k < K.

import time

def search_for_cycles(Family, K_low, K_high):

    file_name = 'output_' + Family.__name__ + '.txt'
    f = open(file_name, 'w')
    start = time.time()
    
    # Instantiate the family
    (t, p, q) = Family()
    print("Starting family: " + str(Family.__name__), file=f)
    print("t(X) = " + str(t), file=f)
    print("p(X) = " + str(p), file=f)
    print("q(X) = " + str(q), file=f)
    
    # Find the candidate embedding degrees up to K that are compatible with this family
    (embedding_degrees, modular_conditions) = candidate_embedding_degrees(Family, K_low, K_high)
    print("Candidate embedding degrees: " + str(embedding_degrees), file=f)
    for k in embedding_degrees:
        print(("For k = " + str(k) + ", necessarily x = " +str(modular_conditions[k])) + " (mod " + str(k) + ")", file=f)
    print("========================", file=f)
    
    # For each potential embedding degree, find the bounds N_left, N_right and perform exhaustive search within [N_left, N_right].
    for k in embedding_degrees:
        
        f.close()
        f = open(file_name, 'a')
        start_k = time.time()
        
        print("k = " + str(k), file=f)
        (N_left, N_right) = compute_bounds(p^k, q)
        print("N_left = " + str(N_left) + ", N_right = " + str(N_right), file=f)
        
        curves = exhaustive_search(Family, k, N_left, N_right, modular_conditions[k])
        print("Curves with embedding degree " + str(k) + " that form a cycle with a curve from the " + str(Family.__name__) + " family: " + str(len(curves)), file=f)
        
        for curve in curves:
            (x, k, tx, px, qx) = curve
            print("x = " + str(x), file=f)
            print("embedding degree = " + str(k), file=f)
            print("t(x) = " + str(tx), file=f)
            print("p(x) = " + str(px), file=f)
            print("q(x) = " + str(qx), file=f)
            print("------------", file=f)
        
        end_k = time.time()
        print('Computations for embedding degree ' + str(k) + ' took', round(end_k - start_k, 2), 'seconds.', file=f)
        print("------------------------", file=f)

    end = time.time()
    print("========================", file=f)
    print('Overall computation took', round(end - start, 2), 'time', file=f)

    f.close()

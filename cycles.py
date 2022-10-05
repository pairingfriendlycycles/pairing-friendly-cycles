#!/usr/bin/env python
# coding: utf-8

# In[1]:


# SETUP

# Define the polynomial rings over the reals and rationals
R.<X> = PolynomialRing(RR, 'X')
Q.<X> = PolynomialRing(QQ, 'X') 

# Curve families
def MNT3():
    t = Q(6*X -1)
    q = Q(12*X^2 - 1)
    n = q + 1 - t
    return(t, n, q)

def MNT4():
    t = Q(-X)
    q = Q(X^2 + X + 1)
    n = q + 1 - t
    return(t, n, q)

def MNT6():
    t = Q(2*X + 1)
    q = Q(4*X^2 + 1)
    n = q + 1 - t
    return(t, n, q)

def Freeman():
    t = Q(10*X^2 + 5*X + 3)
    q = Q(25*X^4 + 25*X^3 + 25*X^2 + 10*X + 3)
    n = q + 1 - t
    return(t, n, q)

def BN():
    t = Q(6*X^2 + 1)
    q = Q(36*X^4 + 36*X^3 + 24*X^2 + 6*X + 1)
    n = q + 1 - t
    return(t, n, q)


# In[2]:


# CANDIDATE EMBEDDING DEGREES

# INPUT: a parametrization of a family of pairing-friendly elliptic curves with prime order.
#        a bound K on the embedding degree to look for.
# OUTPUT: a list of potential embedding degrees k such that 3 <= k <= K and a curve from the
#         family *might* form a cycle with a curve with embedding degree k, along with conditions
#         on x mod k for each of these k.

def candidate_embedding_degrees(Family, K):
    
    (t, n, q) = Family()
    # Create an empty list to store the candidate embedding degrees
    embedding_degrees = []
    # Create an empty list to store the lists of modular conditions for each k
    modular_conditions = [None] * (K+1)
    
    # Embedding degree k implies that q(x) = 1 (mod k). 
    # We check this condition in 0, ..., k-1 and build a list of candidates
    # such that any x has to be congruent to one of them modulo k.
    for k in range(3, K+1):
        
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


# In[3]:


# AUXILIARY FUNCTIONS

def is_integer_valued(p):
    
    # Check if evaluation is integer in deg(p) + 1 consecutive points
    for x in range(p.degree()+1):
        if (not p(x) in ZZ):
            print(str(p) + " is not integer-valued.")
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


# In[4]:


# COMPUTATION OF THE BOUNDS A, B

# INPUT: two integer-valued polynomials a, b in Q[X].
# OUTPUT: bounds A, B in Z, as described in Lemma ?.

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
    sigma_B = sign(r.leading_coefficient())
    sigma_A = sigma_B * (-1)^(r.degree())
    
    # We compute the polynomials w_A, w_B such that 
    # 0 <= w_A < b(x) for all x < A, and
    # 0 <= w_B < b(x) for all x > B.
    w_A = c * r + ((1 - sigma_A) / 2) * b
    w_B = c * r + ((1 - sigma_B) / 2) * b
    
    # Compute A, B
    A = find_relevant_root(w_A, b, -1)
    B = find_relevant_root(w_B, b, 1)
    
    return (A, B)


# In[5]:


# EXHAUSTIVE SEARCH

# INPUT: a parametrization of a family of pairing-friendly elliptic curves with prime order.
#        an embedding degree k.
#        bounds A, B.
# OUTPUT: a list of integers x in [A, B] such that the curve parameterized by (t(x), n(x), q(x))
#         forms a cycle with a curve with embedding degree k.

def exhaustive_search(Family, k, A, B, mod_cond):
    
    (t, n, q) = Family()
    curves  = []
    
    for x in range(A, B+1):
        # We skip those values that will never yield q(x) = 1 (mod k), as precomputed above.
        if (not (x % k) in mod_cond): continue
        # Check the embedding degree condition
        if (n(x)^k - 1 % q(x) == 0):
            curves.append((x, k, t(x), n(x), q(x)))
    
    return curves


# In[6]:


# MAIN FUNCTION

# INPUT: a parameterization of a family of pairing-friendly ellipitc curves with prime order.
#        a bound K on the embedding degree to look for
# OUTPUT: all the cycles involving a curve from the family and a prime-order curve with embedding degree k < K.

def search_for_cycles(Family, K):
    
    # Instantiate the family
    (t, n, q) = Family()
    print("Starting family: " + str(Family.__name__))
    print("t(X) = " + str(t))
    print("n(X) = " + str(n))
    print("q(X) = " + str(q))
    
    # Find the candidate embedding degrees up to K that are compatible with this family
    (embedding_degrees, modular_conditions) = candidate_embedding_degrees(Family, K)
    print("Candidate embedding degrees: " + str(embedding_degrees))
    for k in embedding_degrees:
        print(("For k = " + str(k) + ", necessarily x = " +str(modular_conditions[k])) + " (mod " + str(k) + ")")
    print("=======================")
    
    # For each potential embedding degree, find the bounds A, B and perform exhaustive search within [A, B].
    for k in embedding_degrees:
        
        print("k = " + str(k))
        (A, B) = compute_bounds(n^k, q)
        print("A = " + str(A) + ", B = " + str(B))
        
        curves = exhaustive_search(Family, k, A, B, modular_conditions[k])
        print("Curves with embedding degree " + str(k) + " that form a cycle with a curve from the " + str(Family.__name__) + " family: " + str(len(curves)))
        
        for curve in curves:
            (x, k, t, n, q) = curve
            print("x = " + str(x))
            print("embedding degree = " + str(k))
            print("t(x) = " + str(t))
            print("n(x) = " + str(n))
            print("q(x) = " + str(q))
            print("-----------------------")


# In[ ]:





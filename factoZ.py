# Implémentation de l'algorithme de factorisation dans Z[X]

#I. Représentation de polynômes

# Exemple : X^4+1. P[-1] est le coefficient dominant.
P_ex = [1,0,0,0,1]

# Degré de P
def deg(P) :
    return len(P)-1

# Coefficient dominant
def cd(P) :
    return P[-1]

# <<Actualisation>> du polynôme
# On retire les coefficients non nuls (en partant de la fin)
def maj(P) :
    i=deg(P)
    while (i>=0) and P[i]==0 :
        P.pop()
        i=i-1

# Copie d'un polynôme
def copy(a) :
    n = deg(a)
    return [a[i] for i in range(n+1)]

# Renverser la liste (pour la matrice de Sylvester)
def flip(a) :
    n = deg(a)
    return [a[n-i] for i in range(n+1)]

# Dériver le polynôme
def dv(a) :
    n = deg(a)
    return [ (i+1) * a[i+1] for i in range(n) ] 

# Ajouter des coefficients nuls
def homog(a,N) :
    return a + [0 for i in range(N-deg(a))]

# Réduit du polynôme
def reduit(a) :
    n=deg(a)
    an=cd(a)
    return [ an**(n-1-k)*a[k] for k in range(n) ] + [1]

# Opération inverse du réduit
# Nécessite de prendre en entrée le coefficient dominant
def anti_reduit(a,coef) :
    n=deg(a)
    return [ a[k] // (coef**(n-1-k)) for k in range(n) ] + [coef]

#II. Opérations algébriques

# Somme de polynômes
def somme(a,b,p) :
    n=deg(a)
    m=deg(b)
    c = [ (a[i]+b[i])%p for i in range(min(n,m)+1) ]
    if n<=m :
        c += [ b[i]%p for i in range(n+1,m+1) ]
    else :
        c += [ a[i]%p for i in range(m+1,n+1) ]
    maj(c)
    return c

# Produit de polynômes
def produit(a,b,p) :
    maj(a)
    maj(b)
    n=deg(a)
    m=deg(b)
    if n==-1 or m==-1 :
        return []
    else :
        pr = [ 0 for i in range(n+m+1) ]
        for i in range(n+1) :
            for j in range(m+1) :
                pr[i+j] = (pr[i+j]+a[i]*b[j])%p
        maj(pr)
        return pr
# Multiplication et division par un scalaire
def mul_scal(a,x,p) :
    n=deg(a)
    return [ (x*a[i])%p for i in range(n+1) ]
def div_scal(a,x,p) :
    n=deg(a)
    return [ (a[i]//x)%p for i in range(n+1) ]
# Différence de polynômes
def difference(a,b,p) :
    B = mul_scal(b,-1,p)
    return somme(a,B,p)


# Division Euclidienne

def div_euc(a,b,p) :
    maj(a)
    maj(b)
    n=deg(a)
    m=deg(b)
    if m==-1 :
        raise Exception("Division by 0")
    elif n==-1 :
        return ([],[])
    else :
        r = copy(a)
        q = [0 for i in range(n-m+1)]
        while n >= m :
            q[n-m] = cd(r)
            for i in range(m+1) :
                # Retirer cd(r)/cd(b)*X^(n-m)*b à r
                r[n-m+i] = (r[n-m+i] - (cd(r)*b[i])//b[-1])%p
            r.pop()
            maj(r)
            n = deg(r)
        return (q,r)
def div_euc_Z(a,b) :
    maj(a)
    maj(b)
    n=deg(a)
    m=deg(b)
    if m==-1 :
        raise Exception("Division by 0")
    elif n==-1 :
        return ([],[])
    else :
        r = copy(a)
        q = [0 for i in range(n-m+1)]
        while n >= m :
            q[n-m] = cd(r)
            for i in range(m+1) :
                # Retirer cd(r)/cd(b)*X^(n-m)*b à r
                r[n-m+i] = (r[n-m+i] - (cd(r)*b[i])//b[-1])
            r.pop()
            maj(r)
            n = deg(r)
        return (q,r)


def reste_div_euc(a,b,p) :
    q,r=div_euc(a,b,p)
    return r
def reste_div_euc_Z(a,b) :
    q,r=div_euc_Z(a,b)
    return r
def quotient(a,b,p) :
    q,r=div_euc(a,b,p)
    return q
def quotient_Z(a,b) :
    q,r=div_euc_Z(a,b)
    return q


# III. Préliminaires
import numpy as np
import sympy as sy
sy.init_printing(use_unicode=True)
import math

def det(A) :
    return np.linalg.det(A)

def Sylvester(a,b) :
    n,m=deg(a),deg(b)
    A=flip(a)
    B=flip(b)
    S = np.array([
        ( [0 for k in range(i)] + A + [0 for k in range(m-i-1)] )
        for i in range(m) ] + [
        ( [0 for k in range(i)] + B + [0 for k in range(n-i-1)] )
        for i in range(n)
    ], dtype='int64')
    return S

def Res(a) :
    return round(det( Sylvester(a,dv(a)) ))

# Recherche de p, premier, ne divisant pas Res(a)

def is_prime(N) :
    sq = math.floor(math.sqrt(N))
    for i in range(2, sq+1) :
        if N%i == 0 :
            return False
    return True

def non_div_prime(n) :
    N=abs(n)
    for i in range(5,N) :
        if N%i != 0 :
            if is_prime(i) :
                return i

# Complexité : somme_{i=2}^{N} (i*sqrt(i)) = O(N^3)


## IV. Lemme de BERLEKAMP

def gen(k,p) :
    pol = [ 0 for i in range(p*k+1) ]
    pol[p*k] = 1
    pol[k] = pol[k] -1
    return pol

def calcul_S(a,p) :
    n = deg(a)
    return np.array([
       homog(reste_div_euc(gen(i,p),a,p),(n-1)) for i in range(n)
    ], dtype='int64')



#### Réduite de Gauss-Jordan
##
### Échange de deux lignes
##def echange(s,i,j) :
##    t = copy(s[i])
##    s[i] = copy(s[j])
##    s[j] = t
##
### Multiplication d'une ligne par un scalaire
##def mult_scal_ligne(s,i,x,p) :
##    m = len(s[i])
##    for j in range(m) :
##        s[i][j] = (x*s[i][j])%p
##
### Division par un scalaire, en restant dans Mn(Z)
##def div_scal_ligne(s,i,x) :
##    n = len(s)
##    m = len(s[i])
##    for l in range(n) :
##        if l!= i :
##            for j in range(m) :
##                s[l][j] = (x*s[l][j])
##
### Ajout : Li <- x*L_l + L_i
##def ajout(s,i,l,x,p) :
##    m = len(s[i])
##    for j in range(m) :
##        s[i][j] = (s[i][j] + x*s[l][j])%p
##
### Matrice modulo p
##def mod_p(s,p) :
##    n=len(s)
##    m=len(s[0])
##    for i in range(n) :
##        for j in range(m) :
##            s[i][j] = s[i][j]%p
##
###Gauss-Jordan
##def gauss_jordan(s) :
##    n=len(s)
##    m=len(s[0])
##    r=-1
##    for j in range(m) :
##        i0 = r+1
##        for i in range(r+1,n) :
##            if abs(s[i][j])>abs(s[i0][j]) :
##                i0=i
##        # s[k][j] est le pivot
##        k=i0
##        if s[k][j] != 0 :
##            r = r+1
##            div_scal(s,k,s[k][j])
##            if k!=r :
##                echange(s,k,r)
##            for i in range(n) :
##                if i != r :
##                    ajout(s,i,r, ( - s[i][j] // s[r][j]))
##

def integernullspace(S,p) :
    s = sy.Matrix(S)
    Ker = s.nullspace(simplify=True)
    for vect in Ker :
        factor = 1
        for x in vect :
            n,d = sy.fraction(x)
            factor = sy.lcm(factor, d)
        for i in range(len(vect)) :
            vect[i] = (factor*vect[i])%p
    return Ker

def verdict(S,p) :
    Ker = integernullspace(S,p)
    for vect in Ker :
        for j in range(1,len(vect)) :
            if vect[j] != 0 :
                return ('OK', vect)
    return ('irréductible', [])

def pgcd(a,b,p) :
    q=b
    r=a
    while deg(r)!=-1 :
        s = reste_div_euc(q,r,p)
        q = copy(r)
        r = s
    return q

def pgcd_Z(a,b) :
    q=b
    r=a
    while deg(r)!=-1 :
        s = reste_div_euc_Z(q,r)
        q = copy(r)
        r = s
    return q

def bezout(a,b,p):
    if b == [] :
        return [1],[]
    else :
        q,r=div_euc(a,b,p)
        u,v = bezout(b,r,p)
        return v, somme(u, produit(mul_scal(q,-1,p),v,p),p)

# BERLEKAMP
def Berlekamp(f,p) :
    S=calcul_S(f,p)
    (m,g) = verdict(S,p)
    if m == 'OK' :
        L = [ pgcd(f,somme(g,[-alpha],p),p) for alpha in range(p) ]
        for h in L :
            if deg(h) >= 1 :
                q,_ = div_euc(f,h,p)
                return (h,q)
    return (f,[1])

# HENSEL
def Hensel(f,g,h,u,v,p,k) :
    K = p**k
    K2 = K**2
    r = div_scal(difference(f,produit(g,h,K2),K2),K,K2)
    maj(r)
    h2 = somme(h, mul_scal(reste_div_euc(produit(u,r,K2),h,K2),K,K2),K2)
    g2 = somme(g, mul_scal(reste_div_euc(produit(v,r,K2),g,K2),K,K2),K2)
    u2 = reste_div_euc(difference(mul_scal(u,2,K2),produit(produit(u,u,K2),g2,K2),K2),h2,K2)
    v2 = reste_div_euc(difference(mul_scal(v,2,K2),produit(produit(v,v,K2),h2,K2),K2),g2,K2)
    return (g2,h2,u2,v2)

# MIGNOTTE-LANDAU
def norme2(f) :
    s = 0
    n=deg(f)
    for i in range(n+1) :
        s += f[i]**2
    return math.ceil(math.sqrt(s))
def normeinf(f) :
    m=0
    n=deg(f)
    for i in range(n+1) :
        if abs(f[i]) > m :
            m = abs(f[i])
    return m

def BML(f,p) :
    n = deg(f)
    borne  = math.sqrt(n+1)*math.comb(n,n//2)*norme2(f)
    return math.log(borne,p)


def ajuste_coefs(f,p) :
    def aux(x) :
        if x >= p//2 :
            return x-p
        else :
            return x
    return [ aux(f[i]) for i in range(deg(f)+1) ]

# FACTORISER

MAX_FLOAT = float("inf")

def Factoriser(f) :
    n=deg(f)
    R=Res(f)
    if R == 0 :
        print("f possède un facteur carré :")
        return pgcd_Z(f,dv(f))
    else :
        F = reduit(f)
        p = non_div_prime(R)
        g,h=Berlekamp(F,p)
        print("Factorisation modulo "+str(p)+" :", g,h)
        u,v = bezout(g,h,p)
        print("Coefficients de Bézout :", u,v)
        k = 1
        B = BML(F,p)
        while k <= B :
            g,h,u,v = Hensel(F,g,h,u,v,p,k)
            print("Factorisation modulo "+str(p**(2*k))+" :",g,h)
            k = 2*k
        g = ajuste_coefs(g,p**k)
        h = ajuste_coefs(h,p**k)
        G = pgcd_Z(F,g)
        H = pgcd_Z(F,h)
        if deg(G) == 0 or deg(G) == n:
            if deg(H) == 0 or deg(H) == n:
                print()
                print("Bilan : f est irréductible sur Z[X]")
                return (f,[1])
            else :
                print()
                print("Bilan : f est factorisable sur Z[X]")
                H = anti_reduit(H, cd(f))
                q = quotient_Z(f,H)
                return (q, quotient_Z(f,q))
        else :
            print()
            print("Bilan : f est factorisable sur Z[X]")
            G = anti_reduit(G, cd(f))
            q = quotient_Z(f,G)
            return (q, quotient_Z(f,q))


#GRAPHIQUES
import matplotlib.pyplot as plt

def taille_des_facteurs_Hensel(f,p,N) :
    n=deg(f)
    g,h=Berlekamp(f,p)
    u,v = bezout(g,h,p)
    normes = []
    normes.append(norme2(g))
    i = 0
    while i < N:
        k = 2**i
        g,h,u,v = Hensel(f,g,h,u,v,p,k)
        i += 1
        normes.append(norme2(g))
    B = math.ceil(math.sqrt(n+1)*math.comb(n,n//2)*norme2(f))
    plt.plot(range(N+1),normes, 'b', range(N+1), [B for i in range(N+1)]) 
    plt.show()


# Exemples
Q = [5,13,18,7,7,1]


def gen_rand(M=20,taille=8) :
    F = np.random.randint(M,size=taille)
    F = np.append(F,1)
    R = Res(F)
    p = non_div_prime(R)
    return (F,p)






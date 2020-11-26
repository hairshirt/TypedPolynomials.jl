using DataStructures

# Utility functions
LT(f) = leadingterm(f)
LTS(F) = [LT(f) for f in F]
LM(f) = leadingmonomial(f)
LMS(F) = [LM(f) for f in F]
LC(f) = leadingcoefficient(f)
LCS(F) = [LC(f) for f in F]
Xγ(f1, f2) = lcm(LM(f1), LM(f2))
Lpart(f1, f2) = div(Xγ(f1, f2), LT(f1)) * f1
Spoly(f1, f2) = Lpart(f1, f2) - Lpart(f2, f1)
critpairs(n) = [(i, j) for i in 1:n for j in i:n if i != j]


"Simple Buchberger's Algorithm from Cox, Little, O'Shea"
function buchberger(F)
    G = copy(F)
    while true
        Gprime = G
        for i in 1:length(Gprime)
            for j in i:length(Gprime)
                if i != j
                    r = Spoly(Gprime[i], Gprime[j])
                    println()
                    println("S-Polynomial ($i: $(Gprime[i]), $j: $(Gprime[j])): $r")
                    println()
                    for g in Gprime
                        rmdr = rem(r, g)
                        if ~iszero(rmdr)
                            if ~any(g->monomials(g) == monomials(rmdr), Gprime)
                                push!(G, rmdr)
                                println("rmdr added: $(rmdr)")
                            end
                        end
                    end
                end
            end
        end
        if G == Gprime
            return G
        end
    end
end

function REDPOL(f, P)
    qp = Any[0 for p in P]
    g = copy(f)
    for i in 1:length(P)
        m = rem(g, P[i])
        g = g - m*P[i]
        qp[i] += m
    end
    return (qp, g)
end

function REDUCTION(P)
    Q = OrderedSet(copy(P))
    for p in P
        if p ∈ Q
            Q = setdiff(Q, Set([p]))
            for q in Q
                h = rem(p, q)
                if ~iszero(h)
                    Q = union(Q, Set([h]))
                end
            end
        end
    end
    [LC(q)^(-1) * q for q in Q]
end
        
function GROEBNERTEST(G)
    B = OrderedSet(g1, g2) for g1 in G[1:end-1] for g2 in G[2:end] if g1 ≠ g2)
    
@polyvar x[1:3]

MONOMIAL_ORDER = :grevlex

f = 4x[1]*x[2]^2*x[3] + 4x[3]^2 - 5x[1]^3 + 7x[1]^2*x[3]^2
f1 = 1//1*x[1]^3 - (2//1)*x[1]*x[2]
f2 = 1//1*x[1]^2*x[2] - (2//1)*x[2]^2 + 1//1*x[1]
f3 = -(1//1)x[1]^2
I = [f1, f2, f3]

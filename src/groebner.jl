using DataStructures

# Utility functions
LT(f) = leadingterm(f)
LTS(F) = [LT(f) for f in F]
LM(f) = leadingmonomial(f)
LMS(F) = [LM(f) for f in F]
LC(f) = leadingcoefficient(f)
LCS(F) = [LC(f) for f in F]
LCMLM(f1, f2) = lcm(LM(f1), LM(f2))
Lpart(f1, f2) = div(LCMLM(f1, f2), LT(f1)) * f1
spoly(f1, f2) = Lpart(f1, f2) - Lpart(f2, f1)
critpairs(n) = [(i, j) for i in 1:n for j in i:n if i != j]

function isgrobner(F::Array{T}) where {T <: AbstractPolynomialLike}
    for (i, f1) in enumerate(F)
        for f2 in F[i+1:end]
            s = spoly(f1, f2)
            _, s = divrem(s, F)
            if !iszero(s)
                return false
            end
        end
    end
    return true
end

function buchberger(I::Array{T}) where {T <: AbstractPolynomialLike}
    F = copy(I)
    pairs = [(f1, f2) for (i, f1) in enumerate(F) for f2 in F[i+1:end] if f1 ≠ f2]

    while !isempty(pairs)
        (f1, f2) = pop!(pairs)
        s = spoly(f1, f2)
        _, s = divrem(s, F)
        if !isapproxzero(s)
            for f in F
                push!(pairs, (s, f))
            end
            push!(F, s)
        end
    end

    G = Array{T}(undef, 0)
    while !isempty(F)
        f = pop!(F)
        _, r = divrem(f, vcat(F, G))
        if !isapproxzero(r)
            push!(G, r)
        end
    end

    return G
end

function mindegpairs(F::Array{T}) where {T <: AbstractPolynomialLike}
    G = [((f1, f2), degree(spoly(f1, f2)))
         for (i, f1) in enumerate(F) for f2 in F[i+1:end] if f1 ≠ f2]
    return G
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
                if ~isapproxzero(h)
                    Q = union(Q, Set([h]))
                end
            end
        end
    end
    [LC(q)^(-1) * q for q in Q]
end
        
function GROEBNERTEST(G)
    B = OrderedSet((g1, g2) for g1 in G[1:end-1] for g2 in G[2:end] if g1 ≠ g2)
    while ~isempty(B)
        b = pop!(B)
        h = spoly(b[1], b[2])
        for g in G
            if isapproxzero(rem(h, g))
                continue
            else
                return false
            end
        end
    end
    true
end

function GROEBNER(F)
    G = F
    B = Set((g1, g2) for g1 in G[1:end-1] for g2 in G[2:end] if g1 ≠ g2)
    println(B)
    while ~isempty(B)
        b = pop!(B)
        h = spoly(b[1], b[2])
        for g in G
            h0 = rem(h, g)
            if ~isapproxzero(h0)
                B = union(B, Set([(g, h0)]))
                if h0 ∉ G
                    push!(G, h0)
                end
            end
        end
    end
    G
end

function REDGROEBNER(G)
    F = Set(copy(G))
    H = Set()
    while ~isempty(F)
        f0 = pop!(F)
        for f in F
            if divides(LT(f), LT(f0))
                for h in H
                    if divides(LT(h), LT(f0))
                        H = union(H, f0)
                    end
                end
            end
        end
    end
    REDUCTION(H)
end
    
@polyvar x[1:4]

MONOMIAL_ORDER = :grevlex

f = 4x[1]*x[2]^2*x[3] + 4x[3]^2 - 5x[1]^3 + 7x[1]^2*x[3]^2

f1 = x[1]^2 - (2//1)x[2]^2 - (2//1)x[2]*x[3] - x[3]^2
f2 = -x[1]*x[2] + (2//1)*x[2]*x[3] + x[3]^2
f3 = -(1//1)x[1]^2 + x[1]*x[2] + x[1]*x[3] + x[3]^2
F = [f1, f2, f3]

i1 = (-3//1)*x[1]^3 + x[2]
i2 = (1//1)x[1]^2*x[2] - x[3]
I = [i1, i2]

g1 = (1//1)*x[1]^2 + x[2]^2 + x[3]^2 - (1//1)
g2 = (1//1)*x[1]^2 - x[2] + x[3]^2
g3 = (1//1)*x[1] - x[3]

G = [g1, g2, g3]

h1 = (3//1)*x[1]^2 + (2//1)*x[2]*x[3] - (2//1)*x[1]*x[4]
h2 = (2//1)*x[1]*x[3] - (2//1)*x[2]*x[4]
h3 = (2//1)*x[1]*x[2] - (2//1)*x[3] - (2//1)*x[3]*x[4]
h4 = x[1]^2 + x[2]^2 + x[3]^2 - 1

H = [h1, h2, h3, h4]

using DataStructures
using TypedPolynomials

# Utility functions
LT(f) = leadingterm(f)
LTS(F) = [LT(f) for f in F]
LM(f) = leadingmonomial(f)
LMS(F) = unique([LM(f) for f in F])
LC(f) = leadingcoefficient(f)
LCS(F) = [LC(f) for f in F]
LCMLM(f1, f2) = lcm(LM(f1), LM(f2))
LCMLM(ftuple) = lcm(LM(ftuple[1]), LM(ftuple[2]))
LCMLT(f1, f2) = lcm(LT(f1), LT(f2))
LCMLT(ftuple) = lcm(LT(ftuple[1]), LT(ftuple[2]))
Lpart(f1, f2) = div(LCMLM(f1, f2), LT(f1)) * f1
Mpart(f1, f2) = div(LCMLM(f1, f2), LT(f1))
spoly(f1, f2) = Lpart(f1, f2) - Lpart(f2, f1)
allpairs(s) = [(i, j) for i in 1:s for j in i+1:s if i ≠ j]
Mon(L) = unique(collect(Iterators.flatten([monomials(l) for l in L])))
row2poly(mat, row, monoms) = polynomial(mat[row, :] .* Mon(monoms))
rows(N, monoms) = [row2poly(N, i, monoms) for i in 1:size(N)[1]]


"Return sorted minimum degree pairs by LCMLM"
function mindegpairs(F::Array{T}) where {T <: AbstractPolynomialLike}
    map(x->x[1], sort([((f1, f2), degree(LCMLM(f1, f2)))
                       for (i, f1) in enumerate(F) for f2 in F[i+1:end] if f1 ≠ f2],
                      lt=(mdp1, mdp2) -> mdp1[2] < mdp2[2] ? true : false,
                      rev=true))
end

"Normal selection strategy"
function Select(B, G)
    min = Inf
    for pair in B
        d = degree(LCMLM(G[pair[1]], G[pair[2]]))
        if d < min
            min = d
        end
    end

    minpairs = []
    polys = []
    for pair in B
        d = degree(LCMLM(G[pair[1]], G[pair[2]]))
        if d == min
            push!(minpairs, pair)
            push!(polys, (G[pair[1]], G[pair[2]]))
        end
    end
    (minpairs, polys)
end

"Basic F4 from CLO"
function F4(F::Array{T}) where {T <: AbstractPolynomialLike}
    G = copy(F)
    t = length(G)
    B = allpairs(t)
    count = 0
    while !isempty(B)
        Bprime, polys = Select(B, G)
        B = setdiff(B, Bprime)
        L₁ = [Lpart(pair[1], pair[2]) for pair in polys]
        L₂ = [Lpart(pair[2], pair[1]) for pair in polys]
        L = unique(cat(L₁, L₂, dims=1))
        M, monoms = ComputeM(L, G)
        N = RREF(M)
        Nplus = [p for p in rows(N, monoms) if LM(p) ∉ LMS(rows(M, monoms)) && !isapproxzero(p)]
        for n in Nplus
            G = union(G, [n])
            t = length(G)
            B = union(B, [(i, t) for i in 1:t-1])
        end
    end
    G
end

function ComputeM(L, G)
    H = copy(L)
    done = Set(LMS(H))
    MonH = Set(Mon(H))

    while MonH ≠ done
        xβ = maximum(setdiff(Mon(H), done))
            
        done = union(done, [xβ])
        for f in G
            if divides(LM(f), xβ)
                H = union(H, [div(xβ, LM(f)) * f])
                MonH = union(MonH, Mon(H))
            end
        end
    end
    t = typeof(coefficients(G[1])[1])
    M = zeros(t, length(H), length(MonH))
    for (i, poly) in enumerate([zip(coefficients(h), monomials(h)) for h in H])
        for (coeff, monom) in poly
            for (j, m) in enumerate(MonH)
                if monom == m
                    M[i, j] = coeff
                end
            end
        end
    end
    return M, MonH
end

function REF(M)
    A = copy(M)
    r = 0
    rows, cols = size(A)
    for i in 1:cols
        piv_found = false
        for j in r+1:rows
            if A[j, i] ≠ 0
                r += 1
                A[j, :], A[r, :] = A[r, :], A[j, :]
                A[r, :] *= A[r, i]^-1
                piv_found = true
                break
            end
        end
        if piv_found
            for j in r+1:rows
                A[j, :] -= A[j, i] * A[r, :]
            end
        end
    end
    A
end

function RREF(M)
    A = copy(M)
    rows, cols = size(A)
    r = 0
    for i in 1:cols
        piv_found = false
        for j in r+1:rows
            if A[j, i] ≠ 0
                r += 1
                A[j, :], A[r, :] = A[r, :], A[j, :]
                A[r, :] *= A[r,i]^-1
                piv_found = true
                break
            end
        end
        if piv_found
            for j in [n for n in 1:rows if n != r]
                A[j, :] -= A[j, i] * A[r, :]
            end
        end
    end
    A
end

"Reduce a polynomial modulo P"
function REDPOL(f, P)
    qp = [0 for p in P]
    g = copy(f)
    while any([divides(LT(p), LT(g)) for p in P])
        for (i, p) in enumerate(P)
            if divides(LT(p), LT(g))
                m = div(g, p)
                g -= m*p
                qp[i] += m
            end
        end
    end
    @assert maximum(LTS(qp .* P)) ≤ LT(f)
    (qp, g)
end

"Reduce a system of Polynomials"
function REDUCTION(P)
    Q = copy(P)
    for p in Q
        if any([divides(LT(q),LT(p)) for q in setdiff(Q, [p])])
            setdiff!(Q, [p])
            h = rem(p, Q)
            if ~isapproxzero(h)
                union!(Q, [h])
            end
        end
    end
    [LC(q)^(-1) * q for q in Q]
end

"Test if a system of polynomials is a Groebner basis"
function GROEBNERTEST(G)
    B = mindegpairs(G)
    while !isempty(B)
        g1, g2 = pop!(B)
        h = spoly(g1, g2)
        h = rem(h, G)
        if !isapproxzero(h)
            println("h reduced by G: $h")
            return false
        end
    end
    true
end

"Basic Buchberger algorithm"
function GROEBNER(F)
    G = copy(F)
    B = mindegpairs(G)
    while !isempty(B)
        g1, g2 = pop!(B)
        h = spoly(g1, g2)
        h = rem(h, G)
        if !isapproxzero(h)
            for g in G
                union!(B, Set([(g, h)]))
            end
            union!(G, [h])
        end
    end
    G
end

"Produce unique Reduced Groebner Basis"
function REDGROEBNER(G)
    F = copy(G)
    H = Vector{eltype(F)}()
    while ~isempty(F)
        f0 = pop!(F)
        if all([!divides(LM(f), LM(f0)) for f in F]) &&
            all([!divides(LM(h), LM(f0)) for h in H])
            union!(H, [f0])
        end
    end
    REDUCTION(H)
end

function UPDATE(Gold, Bold, h::Polynomial)
    C = [(h, g) for g in Gold]
    D = Vector{Tuple{eltype(h), eltype(h)}}()
    while !isempty(C)
        h, g1 = pop!(C)
        if isdisjoint(variables(LM(h)), variables(LM(g1))) ||
            (all([!divides(LCMLM(p), LCMLM(h, g1)) for p in C]) &&
            all([!divides(LCMLM(p), LCMLM(h, g1)) for p in D]))
            push!(D, (h, g1))
        end
    end

    E = Vector{eltype(D)}()
    while !isempty(D)
        h, g = pop!(D)
        if !isdisjoint(variables(LM(h)), variables(LM(g)))
            push!(E, (h, g))
        end
    end

    Bnew = Vector{eltype(E)}()
    while !isempty(Bold)
        g1, g2 = pop!(Bold)
        if !divides(LM(h), LCMLM(g1, g2)) ||
            LCMLM(g1, h) == LCMLM(g1, g2) ||
            LCMLM(h, g2) == LCMLM(g1, g2)
            push!(Bnew, (g1, g2))
        end
    end
    
    union!(Bnew, E)
    Gnew = Vector{eltype(Gold)}()
    while !isempty(Gold)
        g = pop!(Gold)
        if !divides(LM(h), LM(g))
            union!(Gnew, [g])
        end
    end
    union!(Gnew, [h])
    (Gnew, Bnew)
end

function GROEBNERNEW2(F::Array{T}) where {T <: AbstractPolynomialLike}
    K = copy(F)
    G = Vector{eltype(F)}()
    B = Set{Tuple{eltype(F), eltype(F)}}()
    while !isempty(K)
        h = pop!(K)
        (G, B) = UPDATE(G, B, h)
    end
    while !isempty(B)
        g1, g2 = pop!(B)
        h = spoly(g1, g2)
        h = rem(h, G)
        if !isapproxzero(h)
            (G, B) = UPDATE(G, B, h)
        end
    end
    G
end

function GEBAUERMOLLER(F::Array{T}) where {T <: AbstractPolynomialLike}
    REDGROEBNER(GROEBNERNEW2(F))
end

function EXTGROEBNER(F::Array{T}) where {T <: AbstractPolynomialLike}
    G = copy(F)
    #𝒢 = [(f, REDPOL(f, G)) for f in F]
    B = mindegpairs(G)

    while !isempty(B)
        g1, g2 = pop!(B)
        g = spoly(g1, g2)
        (qp, h) = REDPOL(g, G)
        if !isapproxzero(h)
            union!(B, [(p, h) for p in G])
     #       union!(𝒢, (h, REDPOL(h, F)))
            union!(G, [h])
        end
    end
    
    ℱ = [(f, REDPOL(f, G)) for f in F]
    (G, ℱ)
end

function EXTREDGROEBNER(F::Array{T}) where {T <: AbstractPolynomialLike}
    G = copy(F)
    𝒢 = [(f, f == g ? 1 : 0) for f in F for g in G]
    B = mindegpairs(G)

    while !isempty(B)
        g1, g2 = pop!(B)
        m1 = Mpart(g1, g2)
        m2 = Mpart(g2, g1)
        g = m1*g1 - m2*g2
        (qp, h) = REDPOL(g, setdiff(G, [g]))
        if !isapproxzero(h)
            union!(B, [(p, h) for p in setdiff(G, [g])])
            union!(𝒢, [(h, REDPOL(f, setdiff(G, [g]))[1]) for f in F])
            union!(G, [h])
        end
    end
    
end
    
@polyvar x[1:4]

fz = 4x[1]*x[2]^2*x[3] + 4x[3]^2 - 5x[1]^3 + 7x[1]^2*x[3]^2

f1 = x[1]^2 + x[1]*x[2] - 1.0
f2 = x[1]^2 - x[3]^2
f3 = x[1]*x[2] + 1.0
I = [f1, f2, f3]

g1 = (1//1)*x[1]^2 + x[2]^2 + x[3]^2 - (1//1)
g2 = (1//1)*x[1]^2 - x[2] + x[3]^2
g3 = (1//1)*x[1] - x[3]

G = [g1, g2, g3]

h1 = 3.0*x[1]^2 + 2.0*x[2]*x[3] - 2.0*x[1]*x[4]
h2 = 2.0*x[1]*x[3] - 2.0*x[2]*x[4]
h3 = 2.0*x[1]*x[2] - 2.0*x[3] - 2.0*x[3]*x[4]
h4 = x[1]^2 + x[2]^2 + x[3]^2 - 1.0

H = [h1, h2, h3, h4]

z1 = x[1]*x[2] + x[2]^2
z2 = x[3] + 1//1
z3 = x[2]^3*x[3] + x[1]^2
z4 = x[3]^5*x[2]^2 + 4//1

Z = [z1, z2, z3, z4]

c1 = x[1] + x[2] + x[3] + x[4]
c2 = x[1]*x[2] + x[2]*x[3] + x[3]*x[4] + x[1]*x[4]
c3 = x[1]*x[2]*x[3] + x[2]*x[3]*x[4] + x[3]*x[4]*x[1] + x[4]*x[1]*x[2]
c4 = x[1]*x[2]*x[3]*x[4] - 1//1
Cyclic4 = [c1, c2, c3, c4]


module TypedPolynomials

import MutableArithmetics
const MA = MutableArithmetics

using Reexport
@reexport using MultivariatePolynomials
const MP = MultivariatePolynomials

using DataStructures

using MacroTools
import Base: *, +, -, /, ^, ==,
    promote_rule, show, isless, size, getindex,
    one, zero, iszero, @pure, copy, exponent, vec

using LinearAlgebra
import LinearAlgebra: dot, adjoint
export @polyvar,
    Variable,
    Monomial,
    Term,
    Polynomial,
    variables,
    terms,
    differentiate,
    subs,
    MONOMIAL_ORDER,
    grevlex,
    grlex,
    rlex,
    lex,
    monom_cmp

include("sequences.jl")
import .Sequences: shortest_common_supersequence, mergesorted

include("types.jl")
include("operators.jl")
include("substitution.jl")
include("calculus.jl")
include("conversion.jl")
include("promotion.jl")
include("call.jl")
include("macros.jl")

end # module

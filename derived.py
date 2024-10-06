
from kernel import (
    Expression, # reexport
    Formula, # reexport
    Conditional as _Conditional, 
    Negation as _Negation,
    Existential as _Existential,
    Membership as _Membership,
    AtomicTerm as _AtomicTerm,
    if_intro, # reexport
    if_elim, # reexport
    not_intro as _not_intro,
    double_not_elim, # reexport
    Fact, # reexport
    exists_intro, # reexport,
    exists_elim, # reexport
    substitute_for_atom as substitute_for_atom
)

from itertools import count as _count

def get_fresh_atom():
    return _AtomicTerm()

def get_fresh_atoms(n, /):
    return (_AtomicTerm() for _ in range(n))

def is_an_atom(expression, /):
    return isinstance(expression, _AtomicTerm)

def if_(ϕ, ψ, /):
    return _Conditional(ϕ, ψ)

def if_get_operands(if_ϕ_ψ, /):
    ϕ, ψ = if_ϕ_ψ.get_parts()
    return ϕ, ψ

def is_an_if(formula, /):
    return isinstance(formula, _Conditional)

def not_(ϕ, /):
    return _Negation(ϕ)

def not_get_operand(not_ϕ, /):
    ϕ = not_ϕ.get_parts()[0]
    return ϕ

def is_a_not(formula, /):
    return isinstance(formula, _Negation)

def and_(ϕ, ψ, /):
    return not_(if_(ϕ, not_(ψ)))

def and_get_operands(and_ϕ_ψ, /):
    ϕ, not_ψ = if_get_operands(not_get_operand(and_ϕ_ψ))
    ψ = not_get_operand(not_ψ)
    assert and_ϕ_ψ == and_(ϕ, ψ)
    return ϕ, ψ

def is_an_and(formula, /):
    if not is_a_not(formula):
        return False
    negand = not_get_operand(formula)
    if not is_an_if(negand):
        return False
    _, consequent = and_get_operands(negand)
    return is_a_not(consequent)

def or_(ϕ, ψ, /):
    return if_(not_(ϕ), ψ)

def or_get_operands(or_ϕ_ψ, /):
    not_ϕ, ψ = if_get_operands(or_ϕ_ψ)
    ϕ = not_get_operand(not_ϕ)
    assert or_ϕ_ψ == or_(ϕ, ψ)
    return ϕ, ψ

def is_an_or(formula, /):
    if not is_an_if(formula):
        return False
    antecedent, _ = if_get_operands(formula)
    return is_a_not(antecedent)

def iff(ϕ, ψ, /):
    return and_(if_(ϕ, ψ), if_(ψ, ϕ))

def iff_get_operands(iff_ϕ_ψ, /):
    return if_get_operands(and_get_operands(iff_ϕ_ψ)[0])

def is_an_iff(formula, /):
    if not is_an_and(formula):
        return False
    left_conjunct, right_conjunct = and_get_operands(formula)
    if not is_an_if(left_conjunct) or not is_an_if(right_conjunct):
        return False
    ϕ, ψ = if_get_operands(left_conjunct)
    return if_get_operands(right_conjunct) == ψ, ϕ

def in_(a, b, /):
    return _Membership(a, b)

def in_get_operands(membership, /):
    return membership.get_parts()

def is_an_in(expression, /):
    return isinstance(expression, _Membership)
    
def exists(x, ϕ_of_x, /):
    return _Existential(x, ϕ_of_x)

def exists_get_operands(existential, /):
    return existential.get_parts()

def is_an_exists(expression, /):
    return isinstance(expression, _Existential)

def forall(x, ϕ_of_x, /):
    return not_(exists(x, not_(ϕ_of_x)))

def forall_get_operands(universal, /):
    x, not_ϕ_of_x = exists_get_operands(not_get_operand(universal))
    return x, not_get_operand(not_ϕ_of_x)

def is_a_forall(expression, /):
    if not isinstance(expression, _Negation):
        return False 
    maybe_an_exists = not_get_operand(expression)
    if not is_an_exists(maybe_an_exists):
        return False
    return is_a_not(exists_get_operands(maybe_an_exists)[1])
########

def and_intro(fact_ϕ, fact_ψ, /):
    ϕ, ψ = fact_ϕ.get_formula(), fact_ψ.get_formula()
    return _not_intro(
        if_intro(if_(ϕ, not_(ψ)), lambda if_ϕ_not_ψ: fact_ψ),
        if_intro(if_(ϕ, not_(ψ)), lambda if_ϕ_not_ψ: if_elim(if_ϕ_not_ψ, fact_ϕ))
    ).check(and_(ϕ, ψ))

def and_elim_left(fact_and_ϕ_ψ, /):
    ϕ, ψ = and_get_operands(fact_and_ϕ_ψ.get_formula())
    fact_not_if_ϕ_not_ψ = fact_and_ϕ_ψ.check(not_(if_(ϕ, not_(ψ))))
    return double_not_elim(_not_intro(
            if_intro(not_(ϕ), 
                lambda fact_not_ϕ: if_intro(ϕ, 
                        lambda fact_ϕ: _not_intro(
                            if_intro(ψ, lambda fact_ψ: fact_ϕ), 
                            if_intro(ψ, lambda fact_ψ: fact_not_ϕ)))),
            if_intro(not_(ϕ), lambda fact_not_ϕ: fact_not_if_ϕ_not_ψ))
    ).check(ϕ)


def and_elim_right(fact_and_ϕ_ψ):
    ϕ, ψ = and_get_operands(fact_and_ϕ_ψ.get_formula())
    fact_not_if_ϕ_not_ψ = fact_and_ϕ_ψ.check(not_(if_(ϕ, not_(ψ))))
    return double_not_elim(_not_intro(
        if_intro(not_(ψ), lambda fact_not_ψ: if_intro(ϕ, lambda fact_ϕ: fact_not_ψ)),
        if_intro(not_(ψ), lambda fact_not_ψ: fact_not_if_ϕ_not_ψ))
    ).check(ψ)


def not_intro(fact_if_ϕ_and_ψ_not_ψ):
    ϕ, and_ψ_not_ψ = if_get_operands(fact_if_ϕ_and_ψ_not_ψ.get_formula())
    ψ, _ = and_get_operands(and_ψ_not_ψ)
    return _not_intro(
        if_intro(ϕ, lambda fact_ϕ: and_elim_left(if_elim(fact_if_ϕ_and_ψ_not_ψ, fact_ϕ))),
        if_intro(ϕ, lambda fact_ϕ: and_elim_right(if_elim(fact_if_ϕ_and_ψ_not_ψ, fact_ϕ)))
    ).check(not_(ϕ))


def explosion(fact_and_ϕ_not_ϕ, ψ):
    ϕ, _ = and_get_operands(fact_and_ϕ_not_ϕ.get_formula())
    fact_ϕ = and_elim_left(fact_and_ϕ_not_ϕ)
    fact_not_ϕ = and_elim_right(fact_and_ϕ_not_ϕ)
    return double_not_elim(not_intro(
        if_intro(not_(ψ), lambda not_ψ: 
            and_intro(fact_ϕ, fact_not_ϕ)))).check(ψ)


def or_intro_left(fact_ϕ, ψ):
    ϕ = fact_ϕ.get_formula()
    return if_intro(not_(ϕ), lambda fact_not_ϕ: 
        explosion(and_intro(fact_ϕ, fact_not_ϕ), ψ)
    ).check(if_(not_(ϕ), ψ)).check(or_(ϕ, ψ))


def or_intro_right(ϕ, fact_ψ):
    ψ = fact_ψ.get_formula()
    return if_intro(not_(ϕ), lambda fact_not_ϕ: 
        fact_ψ
    ).check(if_(not_(ϕ), ψ)).check(or_(ϕ, ψ))


def or_elim(fact_and_or_ϕ_ψ_and_if_ϕ_ω_if_ψ_ω):
    ϕ, ψ = or_get_operands(and_get_operands(fact_and_or_ϕ_ψ_and_if_ϕ_ω_if_ψ_ω.get_formula())[0])
    _, ω = if_get_operands(and_get_operands(and_get_operands(fact_and_or_φ_ψ_and_if_φ_ω_if_ψ_ω.get_formula())[1])[0])
    fact_or_ϕ_ψ = and_elim_left(fact_and_or_ϕ_ψ_and_if_ϕ_ω_if_ψ_ω)
    fact_and_if_ϕ_ω_if_ψ_ω = and_elim_right(fact_and_or_ϕ_ψ_and_if_ϕ_ω_if_ψ_ω)
    fact_if_ϕ_ω = and_elim_left(fact_and_if_ϕ_ω_if_ψ_ω)
    fact_if_ψ_ω = and_elim_right(fact_and_if_ϕ_ω_if_ψ_ω)
    def entails_not_ω_not_or_ϕ_ψ(fact_not_ω):
        fact_not_ϕ = not_intro(if_intro(ϕ, lambda fact_ϕ: and_intro(if_elim(fact_if_ϕ_ω, fact_ϕ), fact_not_ω)))
        fact_not_ψ = not_intro(if_intro(ψ, lambda fact_ψ: and_intro(if_elim(fact_if_ψ_ω, fact_ψ), fact_not_ω)))
        fact_not_if_not_ϕ_ψ = not_intro(if_intro(if_(not_(ϕ), ψ), lambda fact_if_not_ϕ_ψ: 
            and_intro(if_elim(fact_if_not_φ_ψ, fact_not_ϕ), fact_not_ψ)))
        return fact_not_if_not_ϕ_ψ.check(not_(or_(ϕ, ψ)))
    return double_not_elim(not_intro(if_intro(not_(ω), lambda fact_not_ω: 
        and_intro(fact_or_ϕ_ψ, entails_not_ω_not_or_ϕ_ψ(fact_not_ω))))
    ).check(ω)


def bivalence(ϕ):
    def entails_not_or_ϕ_not_ϕ_contradiction(fact_not_or_ϕ_not_ϕ):
        ζ = and_(ϕ, not_(ϕ))
        fact_not_ϕ = not_intro(if_intro(ϕ, lambda fact_ϕ: 
            explosion(and_intro(or_intro_left(fact_ϕ, not_(ϕ)), fact_not_or_φ_not_φ), ζ)))
        fact_ϕ = double_not_elim(not_intro(if_intro(not_(ϕ), lambda fact_not_ϕ:
            explosion(and_intro(or_intro_right(ϕ, fact_not_ϕ), fact_not_or_φ_not_φ), ζ))))
        return and_intro(fact_ϕ, fact_not_ϕ)
    return double_not_elim(not_intro(
        if_intro(not_(or_(ϕ, not_(ϕ))), entails_not_or_ϕ_not_ϕ_contradiction))
    ).check(or_(ϕ, not_(ϕ)))


def bicond_intro(fact_and_if_ϕ_ψ_if_ψ_ϕ):
    ϕ, ψ = iff_get_operands(fact_and_if_ϕ_ψ_if_ψ_ϕ.get_formula())
    return fact_and_if_ϕ_ψ_if_ψ_ϕ.check(iff(ϕ, ψ))

def bicond_elim(fact_iff_ϕ_ψ):
    ϕ, ψ = iff_get_operands(fact_iff_ϕ_ψ.get_formula())
    return fact_iff_ϕ_ψ.check(and_(if_(ϕ, ψ), if_(ψ, ϕ)))

def forall_intro(entails_ϕ_of_a, forall_x_ϕ_of_x):

    x, ϕ_of_x = forall_get_operands(forall_x_φ_of_x)
    a = _AtomicTerm()
    ζ = and_(forall_x_φ_of_x, not_(forall_x_φ_of_x))
    return not_intro(if_intro(
        exists(x, not_(ϕ_of_x)),
        lambda fact_exists_x_not_ϕ_of_x: 
            exists_elim(fact_exists_x_not_ϕ_of_x, lambda a, fact_not_ϕ_of_a: 
                    explosion(
                        and_intro(entails_φ_of_a(a).check(substitute_for_atom(x, ϕ_of_x, a)), 
                        fact_not_φ_of_a.check(not_(substitute_for_atom(x, ϕ_of_x, a)))), ζ)))
    ).check(forall_x_φ_of_x)

def forall_elim(fact_forall_x_ϕ_of_x, a):
    x, ϕ_of_x = forall_get_operands(fact_forall_x_ϕ_of_x.get_formula())
    ϕ_of_a = substitute_for_atom(x, ϕ_of_x, a)
    return double_not_elim(not_intro(if_intro(
        not_(ϕ_of_a),
        lambda fact_not_ϕ_of_a: and_intro(
            exists_intro(fact_not_φ_of_a, exists(x, not_(ϕ_of_x))),
            fact_forall_x_ϕ_of_x)))
    ).check(ϕ_of_a)

########

def test_propositional():

    ϕ = _Membership(_AtomicTerm(), _AtomicTerm())
    ψ = _Membership(_AtomicTerm(), _AtomicTerm())
    ω = _Membership(_AtomicTerm(), _AtomicTerm())
    and_intro(Fact._fabricate(ϕ), Fact._fabricate(ψ)).check(and_(ϕ, ψ))
    and_elim_left(Fact._fabricate(and_(ϕ, ψ))).check(ϕ)
    and_elim_right(Fact._fabricate(and_(ϕ, ψ))).check(ψ)
    not_intro(Fact._fabricate(if_(ϕ, and_(ψ, not_(ψ))))).check(not_(ϕ))
    explosion(Fact._fabricate(and_(ϕ, not_(ϕ))), ψ).check(ψ)
    or_intro_left(Fact._fabricate(ϕ), ψ).check(or_(ϕ, ψ))
    or_intro_right(ϕ, Fact._fabricate(ψ)).check(or_(ϕ, ψ))
    or_elim(Fact._fabricate(and_(or_(ϕ, ψ), and_(if_(ϕ, ω), if_(ψ, ω))))).check(ω)
    bivalence(ϕ).check(or_(ϕ, not_(ϕ)))
    bicond_intro(Fact._fabricate(and_(if_(ϕ, ψ), if_(ψ, ϕ)))).check(iff(ϕ, ψ))
    bicond_elim(Fact._fabricate(iff(ϕ, ψ))).check(and_(if_(ϕ, ψ), if_(ψ, ϕ)))

def test_quantifiers():

    ϕ = _Membership(_AtomicTerm(), _AtomicTerm())
    a, b, c, x, y = get_fresh_atoms(5)

    def assert_fails(thunk):
        failed = False
        try:
            thunk()
        except:
            failed = True
        if not failed:
            raise Exception("expected exception but none was received.")

    exists_intro(Fact._fabricate(in_(a, a)), exists(x, in_(x, x))).check(exists(x, in_(x, x)))
    exists_intro(Fact._fabricate(in_(a, a)), exists(x, in_(a, x))).check(exists(x, in_(a, x)))
    exists_intro(Fact._fabricate(exists(x, in_(a, x))), exists(y, exists(x, in_(a, x)))).check(exists(y, exists(x, in_(a, x))))
    exists_intro(Fact._fabricate(exists(x, in_(a, x))), exists(y, exists(x, in_(a, x)))).check(exists(y, exists(x, in_(a, x))))
    exists_intro(Fact._fabricate(exists(x, and_(in_(x, b), not_(in_(b, x))))), 
        exists(y, exists(x, and_(in_(x, y), not_(in_(y, x)))))
    ).check(exists(y, exists(x, and_(in_(x, y), not_(in_(y, x))))))
    exists_intro(Fact._fabricate(in_(a, a)), exists(x, in_(x, x))).check(exists(x, in_(x, x)))
    exists_intro(Fact._fabricate(in_(a, a)), exists(x, in_(a, x))).check(exists(x, in_(a, x)))
    exists_intro(Fact._fabricate(exists(x, in_(a, x))), exists(y, exists(x, in_(a, x)))).check(exists(y, exists(x, in_(a, x))))
    exists_intro(Fact._fabricate(exists(x, in_(a, x))), exists(y, exists(x, in_(a, x)))).check(exists(y, exists(x, in_(a, x))))
    exists_intro(Fact._fabricate(exists(x, and_(in_(x, b), not_(in_(b, x))))), 
        exists(y, exists(x, and_(in_(x, y), not_(in_(y, x)))))
    ).check(exists(y, exists(x, and_(in_(x, y), not_(in_(y, x))))))

    exists_elim(
        Fact._fabricate(exists(x, in_(x, x))), lambda a, fact_in_a_a: exists_intro(exists_intro(fact_in_a_a, exists(x, in_(x, a))), exists(y, exists(x, in_(x, y))))
    ).check(exists(y, exists(x, in_(x, y))))

    assert_fails(lambda: exists_elim(Fact._fabricate(exists(x, in_(x, x))), lambda a, fact_in_a_a: exists_intro(fact_in_a_a, exists(x, in_(x, a)))))
    assert_fails(lambda: exists_intro(Fact._fabricate(forall(x, in_(x, c))), exists(y, forall(x, in_(y, c)))))
    assert_fails(lambda: exists_intro(Fact._fabricate(forall(x, in_(x, x))), exists(y, forall(x, in_(y, y)))))
    assert_fails(lambda: exists_intro(Fact._fabricate(forall(x, in_(x, x))), exists(y, forall(x, in_(x, y)))))
    assert_fails(lambda: exists_intro(Fact._fabricate(forall(x, in_(x, x))), exists(y, forall(x, in_(x, y)))))
    assert_fails(lambda: exists_intro(Fact._fabricate(in_(a, b)), exists(x, in_(x, x))))



    forall_intro(lambda x: or_intro_right(in_(x, x), bivalence(ϕ)), forall(x, or_(in_(x, x), or_(ϕ, not_(ϕ)))))
    forall_elim(Fact._fabricate(forall(x, in_(x, x))), a).check(in_(a, a))

    assert exists_get_operands(exists(x, in_(x, x))) == (x, in_(x, x))
    assert is_an_exists(exists(x, in_(x, x)))
    assert exists_get_operands(exists(x, exists(y, in_(x, y)))) == (x, exists(y, in_(x, y)))
    assert is_an_exists(exists(x, exists(y, in_(x, y))))


def test():

    test_propositional()
    test_quantifiers()

    print("Tests passed.")


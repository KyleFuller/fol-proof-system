import abc as _abc
import weakref as _weakref


def _ensure_class(obj, cls, /):
    if not isinstance(obj, cls):
        raise TypeError(f"Some instance of {cls} was expected.")

def _ensure_all_of_class(objs, cls, /):
    for obj in objs:
        _ensure_class(obj, cls)

def _block_further_subclassing(final_class, /):
    def __init_subclass__(cls, **kwargs):
        raise TypeError(f"Class {final_class} is final and cannot be subclassed.")
    final_class.__init_subclass__ = classmethod(__init_subclass__)

def _raise_abstract_instantiation_error(cls, /):
    raise TypeError(f"Class {cls} is abstract and cannot be instantiated.")

class Expression(_abc.ABC):
    
    _parts: ...

    _instances = _weakref.WeakValueDictionary()

    def __new__(cls, *args, **kwargs):
        key = (cls, args, tuple(sorted(kwargs.items())))
        if key in cls._instances:
            return cls._instances[key]
        instance = super().__new__(cls)
        cls._instances[key] = instance
        return instance

    def __init__(self, *args, **kwargs):
        _raise_abstract_instantiation_error(__class__)

    def get_parts(self):
        return self._parts

class Formula(Expression, _abc.ABC):
    pass

class Conditional(Formula):

    def __init__(self, antecedent, consequent, /):
        _ensure_class(antecedent, Formula)
        _ensure_class(consequent, Formula)
        self._parts = (antecedent, consequent)

_block_further_subclassing(Conditional)

class Negation(Formula):

    def __init__(self, negand, /):
        _ensure_class(negand, Formula)
        self._parts = (negand,)

_block_further_subclassing(Negation)

class Existential(Formula):
    
    def __init__(self, qv, body, /):
        _ensure_class(qv, AtomicTerm)
        _ensure_class(body, Formula)
        self._parts = (qv, body)

_block_further_subclassing(Existential)

class Membership(Formula):

    def __init__(self, member, set, /):
        _ensure_class(member, Term)
        _ensure_class(set, Term)
        self._parts = (member, set)

_block_further_subclassing(Membership)

_block_further_subclassing(Formula)

class Term(Expression, _abc.ABC):
    pass

class AtomicTerm(Term):

    def __new__(cls):
        return object.__new__(cls)

    def __init__(self):
        pass
    
    def get_parts(self):
        return tuple()

_block_further_subclassing(AtomicTerm)

_block_further_subclassing(Term)

_block_further_subclassing(Expression)

class Fact:

    # the top not-so-hypothetical "hypothetical" frame.  Working directly in this frame means working without any hypothetical assumptions.
    _top_frame = object()
    # the set of hypothetical frames that we are working under. 
    _frames = {_top_frame}
    # the current hypothetical frame.
    _frame = _top_frame

    # instance attributes
    _formula: ...
    _home_frame: ...

    @classmethod
    def _fabricate(cls, formula, /):
        _ensure_class(formula, Formula)
        fact = Fact.__new__(Fact)
        fact._formula = formula
        fact._home_frame = Fact._frame
        return fact
    
    def check(self, formula, /):
        self.check_frame()
        if self._formula != formula:
            raise Exception("Fact's formula not as expected.")
        return self
    
    def check_frame(self):
        if self._home_frame not in __class__._frames:
            raise Exception("Fact out of frame.")
        return self
    
    def get_formula(self):
        return self._formula

    def __init__(self, *args, **kwargs):
        raise NotImplementedError("Direct construction not allowed.")
    
    def __eq__(self, other):
        raise NotImplementedError
                
    def __hash__(self):
        raise NotImplementedError

_block_further_subclassing(Fact)

########

def _check_factness(fact, /):
    _ensure_class(fact, Fact)
    fact.check_frame()

def _hypothetically_follow_entailment(antecedent, entailment, /):
    _ensure_class(antecedent, Formula)

    outer_frame = Fact._frame
    inner_frame = object()
    Fact._frame = inner_frame
    Fact._frames.add(inner_frame)
    fact_antecedent = Fact._fabricate(antecedent)
    fact_consequent = entailment(fact_antecedent)
    _check_factness(fact_consequent)
    consequent = fact_consequent._formula
    Fact._frames.remove(inner_frame)
    Fact._frame = outer_frame

    return consequent
    
def if_intro(ϕ, entails_ϕ_ψ, /):
    ψ = _hypothetically_follow_entailment(ϕ, entails_ϕ_ψ)
    return Fact._fabricate(Conditional(ϕ, ψ))

def if_elim(fact_conditional, fact_antecedent, /):
    _check_factness(fact_conditional)
    _check_factness(fact_antecedent)
    ϕ, ψ = fact_conditional.get_formula().get_parts()
    fact_conditional.check(Conditional(ϕ, ψ))
    fact_antecedent.check(ϕ)
    return Fact._fabricate(ψ)
    
def not_intro(fact_conditional_positive, fact_conditional_negative, /):
    _check_factness(fact_conditional_positive)
    _check_factness(fact_conditional_negative)
    ϕ, ψ = fact_conditional_positive.get_formula().get_parts()
    fact_conditional_positive.check(Conditional(ϕ, ψ))
    fact_conditional_negative.check(Conditional(ϕ, Negation(ψ)))
    return Fact._fabricate(Negation(ϕ))

def double_not_elim(fact_double_negation, /):
    _check_factness(fact_double_negation)
    ϕ = fact_double_negation.get_formula().get_parts()[0].get_parts()[0]
    fact_double_negation.check(Negation(Negation(ϕ)))
    return Fact._fabricate(ϕ)

_sfa_cache = _weakref.WeakKeyDictionary()
def _substitute_for_atom(outgoer, exp, incomer, /):

    assumed_type_set = {Conditional, Negation, Existential, Membership, AtomicTerm}
    _ensure_class(exp, Expression)
    assert type(exp) in assumed_type_set
    assert isinstance(outgoer, AtomicTerm)
    assert isinstance(incomer, Term)

    def recur_with_caching(outgoer, exp, incomer, /):

        if not outgoer in _sfa_cache:
            _sfa_cache[outgoer] = _weakref.WeakKeyDictionary()

        from_exp = _sfa_cache[outgoer]

        if not exp in from_exp:
            from_exp[exp] = _weakref.WeakKeyDictionary()

        from_incomer = from_exp[exp]

        if not incomer in from_incomer:
            result = _substitute_for_atom(outgoer, exp, incomer)
            from_incomer[incomer] = result

        result = from_incomer[incomer]

        return result

    if isinstance(exp, AtomicTerm):
        if exp == outgoer:
            return incomer
        return exp
    
    if type(exp) in {Conditional, Negation, Membership}:
        exp_parts = exp.get_parts()
        return type(exp)(*(recur_with_caching(outgoer, part, incomer) for part in exp_parts))
    
    if isinstance(exp, Existential):
        exp_qv, exp_body = exp.get_parts()
        if exp_qv == outgoer:
            return exp
        return type(exp)(exp_qv, recur_with_caching(outgoer, exp_body, incomer))
    
    assert False # should not reach.

def substitute_for_atom(outgoer, exp, incomer, /):

    return _substitute_for_atom(outgoer, exp, incomer)

def _equal_with_early_return(exp1, exp2, early_return, /):
    assumed_type_set = {Conditional, Negation, Existential, Membership, AtomicTerm}
    assert type(exp1) in assumed_type_set and type(exp2) in assumed_type_set
    
    early_return_val = early_return(exp1, exp2) 
    if early_return_val in {True, False}:
        return early_return_val
    assert early_return_val == None
    
    if isinstance(exp1, AtomicTerm):
        return exp1 == exp2

    return (type(exp1) == type(exp2) and 
        len(exp1.get_parts()) == len(exp2.get_parts()) and 
        all(_equal_with_early_return(exp1_part, exp2_part, early_return) for exp1_part, exp2_part in zip(exp1.get_parts(), exp2.get_parts())))

from functools import reduce as _reduce
def _find_free_atoms(exp, /):
    assumed_type_set = {Conditional, Negation, Existential, Membership, AtomicTerm}
    assert type(exp) in assumed_type_set
    if isinstance(exp, AtomicTerm):
        return {exp}
    if type(exp) in {Conditional, Negation, Membership}:
        return set(_reduce(set.union, (_find_free_atoms(part) for part in exp.get_parts())))
    if isinstance(exp, Existential):
        qv, body = exp.get_parts()
        return _find_free_atoms(body).difference({qv})
    assert False # should not reach

def exists_intro(fact_ϕ, existential, /):

    """
    an existential can be introduced from a formula ϕ iff there is some a such that replacing all free occurences of the quantification variable x in the existential body with a results in ϕ.

    another way of stating the necessary and sufficient requirement for being able to introduce the existential is that the body must be equal to ϕ except that wherever x appears FREE in the body, it is instead both allowed and required that a appears there in ϕ.
    """

    _check_factness(fact_ϕ)
    _ensure_class(existential, Existential)

    ϕ = fact_ϕ.get_formula()
    x, body = existential.get_parts()
    
    ϕ_free = _find_free_atoms(ϕ)

    a = None
    def early_return(exp1, exp2):
        nonlocal a
        if exp2 == x:
            if a == None:
                a = exp1
            return exp1 == a and _find_free_atoms(a).issubset(ϕ_free)
        if isinstance(exp2, Existential) and exp2.get_parts()[0] == x:
            return exp1 == exp2
        
    if _equal_with_early_return(ϕ, body, early_return):
        if a != None:
            assert substitute_for_atom(x, body, a) == ϕ
        return Fact._fabricate(Existential(x, body))
    raise Exception("existential body does not match fact given for existential introduction.")

def exists_elim(fact_exists_x_ϕ_of_x, entails_ϕ_of_y_ψ, /):
    _check_factness(fact_exists_x_ϕ_of_x)
    _ensure_class(fact_exists_x_ϕ_of_x.get_formula(), Existential)
    x, ϕ_of_x = fact_exists_x_ϕ_of_x.get_formula().get_parts()
    y = AtomicTerm()
    ψ = _hypothetically_follow_entailment(substitute_for_atom(x, ϕ_of_x, y), lambda fact_ϕ_of_y: entails_φ_of_y_ψ(y, fact_φ_of_y))
    if y in _find_free_atoms(ψ):
        raise Exception("Final formula in existential elimination cannot contain the temporary term.")
    return Fact._fabricate(ψ)
    
from functools import cache as _cache
@_cache
def find_expression_size(exp):
    _ensure_class(exp, Expression)
    assert type(exp) in {Conditional, Negation, Existential, Membership, AtomicTerm}
    if isinstance(exp, AtomicTerm):
        return 1
    if type(exp) in {Conditional, Negation, Existential, Membership}:
        return 1 + sum(find_expression_size(part) for part in exp.get_parts())

    
def find_expression_size_without_repetition(exp):
    _ensure_class(exp, Expression)
    assert type(exp) in {Conditional, Negation, Existential, Membership, AtomicTerm}
    seen = set()

    @_cache
    def find_expression_size_without_repetition_rec(exp):

        if isinstance(exp, AtomicTerm):
            return 1
        if type(exp) in {Conditional, Negation, Existential, Membership}:
            size = 1
            for part in exp.get_parts():
                if part not in seen:
                    size += find_expression_size_without_repetition_rec(part)
                    seen.add(part)
                else:
                    size += 1
            return size
    return find_expression_size_without_repetition_rec(exp)
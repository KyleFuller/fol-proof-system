from derived import get_fresh_atoms, and_, forall, iff, in_, if_, exists, not_, or_
from collections import namedtuple
from kernel import find_expression_size as _find_expression_size, find_expression_size_without_repetition as _find_expression_size_without_repetition

def _get():

    a, b, c, f, i, p, u, v, x, y, ø, s = get_fresh_atoms(12)

    def eq(a, b):
        return forall(s, iff(in_(a, s), in_(b, s)))

    extensionality_axiom = forall(a, forall(b, 
        if_(forall(x, iff(in_(x, a), in_(x, b))),
            eq(a, b))))

    empty_set_axiom = exists(a, forall(x, not_(in_(x, a))))

    pairing_axiom = forall(u, forall(v, exists(a, 
        forall(x, iff(in_(x, a), or_(eq(x, u), eq(x, v)))))))

    union_axiom = forall(f, exists(u, 
        forall(x, iff(in_(x, u), exists(c, and_(in_(c, f), in_(x, c)))))))

    power_set_axiom = forall(a, exists(p, 
        forall(x, iff(in_(x, p), forall(y, if_(in_(y, x), in_(y, a)))))))
    
    def with_(x, property_of_x, ϕ_of_x):
        return forall(x, if_(property_of_x, ϕ_of_x))

    def is_empty(s):
        return forall(x, not_(in_(x, s)))
    
    def is_union_of(a, b, u):
        return forall(x, iff(in_(x, u), or_(in_(x, a), in_(x, b))))
    
    def is_singleton_of(a, s):
        return forall(x, iff(in_(x, a), eq(x, s)))
    
    infinity_axiom = with_(ø, is_empty(ø),
        exists(i,
            and_(in_(ø, i),
                forall(x, with_(u, with_(s, is_singleton_of(x, s), is_union_of(x, s, u)),
                    if_(in_(x, i), in_(u, i)))))))
    
    def is_intersect_of(a, b, i):
        return forall(x, iff(in_(x, i), and_(in_(x, a), in_(x, b))))
    
    regularity_axiom = with_(ø, is_empty(ø), 
        forall(a, if_(not_(eq(a, ø)), 
            exists(x, and_(in_(x, a), 
                with_(i, is_intersect_of(x, a, i), eq(i, ø)))))))
    
    return {'eq': eq, 'extensionality_axiom': extensionality_axiom, 'empty_set_axiom': empty_set_axiom, 'pairing_axiom': pairing_axiom, 'union_axiom': union_axiom, 'power_set_axiom': power_set_axiom, 'infinity_axiom': infinity_axiom, 'regularity_axiom': regularity_axiom}

def test():
        
    _get()

    # eq = stuff['eq']
    # extensionality_axiom = stuff['extensionality_axiom']
    # empty_set_axiom = stuff['empty_set_axiom']
    # pairing_axiom = stuff['pairing_axiom']
    # union_axiom = stuff['union_axiom']
    # power_set_axiom = stuff['power_set_axiom']
    # infinity_axiom = stuff['infinity_axiom']
    # regularity_axiom = stuff['regularity_axiom']

# import cProfile
# cProfile.run('test()')
test()

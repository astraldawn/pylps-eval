from kanren import *

initial = Relation()
final = Relation()
facts(initial, (['l', 'l', 'l', 'l']))
facts(final, (['r', 'r', 'r', 'r']))


P = var()


# def river_aux(A, B, V, P):
#     return run(1, P, (final, P))


# def river(P):
#     start, end = vars(2)
#     return conde(
#         initial(start),
#         final(end),
#         run(1, P, (river_aux, start, end, [start], P))
#     )

# def river(P):
#     return run(
#         1, P,
#         (final, P),
#     )


res = run(1, P, final(P))
print(res)

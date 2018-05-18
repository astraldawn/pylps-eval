from LogicAPI import Term, Var, query, Cut, _, Func, BoolFunc, Object

A, B, V, P = Var('A'), Var('B'), Var('V'), Var('P')
X, Y, Z = Var('X'), Var('Y'), Var('Z')
Action, C, Plan = Var('Action'), Var('C'), Var('Plan')
Start, End = Var('Start'), Var('End')
L2 = Var('L2')
L3 = Var('L3')
H = Var('H')
T = Var('T')
L = Var('L')


class initial(Term):
    pass


class final(Term):
    pass


class crossing(Term):
    pass


class river(Term):
    pass


class river_aux(Term):
    pass


class not_allowed(Term):
    pass


class member(Term):
    pass


+member(X, [X] + _)
member(X, [Y] + T) <= member(X, T)


class not_in(Term):
    pass


+not_in([], L, [])
not_in([X] + Y, L, [X] + L2) <= (~member(X, L)) & Cut() & not_in(Y, L, L2)
not_in([X] + Y, L, L2) <= not_in(Y, L, L2)


+initial(['l', 'l', 'l', 'l'])
+final(['r', 'l', 'r', 'l'])
# +final(['r', 'r', 'r', 'r'])

# +crossing(['l', X, Y, Z], ['r', X, Y, Z], 'farmer_cross')
# +crossing(['r', X, Y, Z], ['l', X, Y, Z], 'farmer_back')

# +crossing(['l', 'l', Y, Z], ['r', 'r', Y, Z], 'fox_cross')
# +crossing(['r', 'r', Y, Z], ['l', 'l', Y, Z], 'fox_back')

+crossing(['l', X, 'l', Z], ['r', X, 'r', Z], 'goose_cross')
# +crossing(['r', X, 'r', Z], ['l', X, 'l', Z], 'goose_back')

# +crossing(['l', X, Y, 'l'], ['r', X, Y, 'r'], 'beans_cross')
# +crossing(['r', X, Y, 'r'], ['l', X, Y, 'l'], 'beans_back')

+river_aux(A, A, _, [])

not_allowed([X, Y, Y, _]) <= (X != Y)
not_allowed([X, _, Y, Y]) <= (X != Y)

river_aux(A, B, V, P) <= (
    crossing(A, C, Action) &
    # ~member(C, V) &  # member does not seem to work correctly
    river_aux(C, B, [C] + V, Plan) &
    (P == [Action] + Plan)
)

river(P) <= (
    initial(Start) &
    final(End) &
    river_aux(Start, End, [Start], P)
)

print(list(query(river(P))))

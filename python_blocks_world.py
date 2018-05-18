from queue import PriorityQueue
from itertools import combinations
from collections import defaultdict
import copy


class State():
    def __init__(self, towers, moves):
        self.towers = sorted(towers)
        self.moves = []

    def __repr__(self):
        ret = "State: %s, Moves: %s" % (str(self.towers), str(self.moves))
        return ret

    def hash(self):
        return str(self.towers)

    def __lt__(self, other):
        return 0


initial_state = State([
    ['floor', 'f', 'b', 'e'],
    ['floor', 'a', 'd', 'c']
], [])

final_state = State([
    ['floor', 'd', 'e', 'f'],
    ['floor', 'c', 'b', 'a']
], [])


def valid_move_combinations(moves, max_simultaneous):
    moves = sorted(moves)
    for i in range(max_simultaneous):
        for proposed_moves in combinations(moves, i + 1):
            seen_d = defaultdict(int)
            valid = True
            for move in proposed_moves:
                if not valid:
                    break

                bf, tf, bt, tt = move

                if seen_d[bf] > 0 or seen_d[bt] > 0:
                    valid = False

                seen_d[bf] += 1
                if bt != 'floor':
                    seen_d[bt] += 1

            if not valid:
                continue

            yield proposed_moves


def solve(start, end):

    states = PriorityQueue()
    states.put((0, 0, start))
    final_hash = final_state.hash()
    max_simultaneous = 2
    seen = set()
    cnt = 0

    while not states.empty():
        time, n_moves, cur_state = states.get_nowait()
        state_hash = cur_state.hash()

        # print(time, n_moves, cur_state)

        if state_hash == final_hash:
            return cur_state

        if state_hash in seen:
            continue

        seen.add(state_hash)

        # Generate individual moves
        towers = cur_state.towers
        towers_len = len(towers)
        possible_moves = set()
        for i in range(towers_len):
            free_block = towers[i][-1]
            if free_block == 'floor':
                continue
            for j in range(towers_len + 1):
                if i == j:
                    continue

                if j == towers_len:
                    possible_moves.add((free_block, i, 'floor', j))
                else:
                    possible_moves.add((free_block, i, towers[j][-1], j))

        # Combine and apply
        for moves in list(
                valid_move_combinations(possible_moves, max_simultaneous)):
            new_state = copy.deepcopy(cur_state)
            towers_len = len(new_state.towers)

            for move in moves:
                bf, tf, bt, tt = move
                new_state.towers[tf] = new_state.towers[tf][:-1]
                new_state.moves.append((bf, bt, time))

                if tt == towers_len:
                    new_state.towers.append([bt, bf])
                    continue

                new_state.towers[tt].append(bf)

            new_state.towers = sorted(
                [t for t in new_state.towers if len(t) > 1])

            states.put((time + 1, len(new_state.moves), new_state))

        # break
        cnt += 1


res = solve(initial_state, final_state)
print(res.moves)

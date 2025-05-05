#!/usr/bin/env python3

"""
Finite state automata and related algorithms.
"""

__author__ = 'johnrickE'


# All automata used here processes input byte-by-byte.
# A byte may range from 0 to 255, giving an alphabet of 256 characters.
NUM_CHARS = 256

# Symbol representing an ε-transition, where an NFA makes a transition without
# consuming any input symbol.
EPSILON = NUM_CHARS


class DFA:
    """
    A deterministic finite state automaton.
    """

    def __init__(self):
        """
        Constructs a new, empty DFA.
        """
        self.transitions = []
        self.outputs = dict()
        self.initial_state = -1
    
    def add_state(self):
        """
        Adds a new state to the DFA.

        :return The newly added state.
        """
        state = len(self.transitions)
        self.transitions.append([-1 for _ in range(0, NUM_CHARS)])
        return state
    
    def is_sink_state(self, state):
        """
        Checks if no accepting state is reachable from the given state.

        :param state    The given state.

        :return True if the given state is a sink state; False otherwise.
        """
        explored = set()
        frontier = {state}
        while len(frontier) > 0:
            state = frontier.pop()
            explored.add(state)
            if len(self.outputs.get(state, set())) > 0:
                return False
            for c in range(0, NUM_CHARS):
                next_state = self.transitions[state][c]
                if next_state not in explored:
                    frontier.add(next_state)
        return True
        
    def union(self, other):
        """
        Uses product construction to compute the union of two DFAs.

        :param  other A DFA to union with this DFA.

        :return A new DFA which is the union of this DFA and the given DFA.
        """
        lhs = self
        rhs = other

        dfa = DFA()
        dfa.initial_state = dfa.add_state()

        state_map = dict()
        frontier = []

        pair = lhs.initial_state, rhs.initial_state
        state_map[pair] = dfa.initial_state
        frontier.append(pair)

        while len(frontier) > 0:
            pair = frontier.pop()
            state = state_map[pair]
            for symbol in range(0, NUM_CHARS):
                next_pair = lhs.transitions[pair[0]][symbol], rhs.transitions[pair[1]][symbol]
                if next_pair not in state_map:
                    state_map[next_pair] = dfa.add_state()
                    frontier.append(next_pair)
                dfa.transitions[state][symbol] = state_map[next_pair]
            
            lhs_outputs = lhs.outputs.get(pair[0], set())
            rhs_outputs = rhs.outputs.get(pair[1], set())
            if len(lhs_outputs) > 0 or len(rhs_outputs) > 0:
                if state not in dfa.outputs:
                    dfa.outputs[state] = set()
                dfa.outputs[state].update(lhs_outputs)
                dfa.outputs[state].update(rhs_outputs)

        return dfa
    
    def minimize(self):
        """
        Creates an equivalent DFA containing the smallest number of states.

        :return A new DFA equivalent to this DFA with a minimal number of states.
        """
        return self # TODO


class NFA:
    """
    A non-deterministic finite state automaton.
    """

    def __init__(self):
        """
        Constructs a new, empty NFA.
        """
        self.next_state = -1
        self.transitions = dict()
        self.outputs = dict()
        self.initial_state = -1
    
    def add_state(self):
        """
        Adds a new state to the NFA.

        :return The newly added state.
        """
        self.next_state += 1
        return self.next_state
    
    def add_transition(self, old_state, new_state, symbol):
        """
        Sets a transition from one state to another on a given symbol.

        :param old_state    The state before transitioning.
        :param new_state    The state after transitioning.
        :param symbol       The input symbol triggering the transition.
        """
        key = (old_state, symbol)
        if key not in self.transitions:
            self.transitions[key] = set()
        self.transitions[key].add(new_state)
    
    def remove_epsilons(self):
        """
        Creates an equivalent NFA with all ε-transitions eliminated.

        :return A new NFA equivalent to this NFA without ε-transitions.
        """
        initial_state = self.initial_state

        nfa = NFA()
        state_ids = dict()

        def get_new_state(state): # Maps state IDs between this ε-NFA and the new NFA.
            nonlocal nfa, state_ids
            if state not in state_ids:
                state_ids[state] = nfa.add_state()
            return state_ids[state]
        
        nfa.initial_state = get_new_state(initial_state)
        frontier = [initial_state]
        explored = set()

        while len(frontier) > 0:
            state = frontier.pop()
            if state in explored:
                continue
            explored.add(state)
            new_state = get_new_state(state)
            for intermediate_state in self.epsilon_closure(state):
                if intermediate_state in self.outputs:
                    nfa.outputs[new_state] = set(self.outputs[intermediate_state])
                for (s, symbol), states in self.transitions.items():
                    if s != intermediate_state or symbol == EPSILON:
                        continue
                    for next_state in states:
                        new_next_state = get_new_state(next_state)
                        nfa.add_transition(new_state, new_next_state, symbol)
                        frontier.append(next_state)

        return nfa
    
    def get_dfa(self):
        """
        Uses powerset construction to create a DFA equivalent to this NFA.

        :return A new DFA equivalent to this NFA.
        """
        dfa = DFA()
        dfa.initial_state = dfa.add_state()

        state_map = dict()
        frontier = []
        
        states = frozenset([self.initial_state])
        state_map[states] = dfa.initial_state
        frontier.append(states)

        while len(frontier) > 0:
            states = frontier.pop()

            for symbol in range(0, NUM_CHARS):
                next_states = set()
                for state in states:
                    next_states.update(self.transitions.get((state, symbol), []))
                next_states = frozenset(next_states)
                if next_states not in state_map:
                    state_map[next_states] = dfa.add_state()
                    frontier.append(next_states)
                dfa.transitions[state_map[states]][symbol] = state_map[next_states]
            
            outputs = set()
            for state in states:
                outputs.update(self.outputs.get(state, []))
            if len(outputs) > 0:
                dfa.outputs[state_map[states]] = outputs

        return dfa
    
    def epsilon_closure(self, state):
        """
        Computes the ε-closure of the given state, which is the set of all
        states reachable from the given state using only ε-transitions.

        :param state    The state used to compute the ε-closure.

        :return A set representing the ε-closure of the given state.
        """
        transitions = self.transitions

        closure = set()
        frontier = [state]

        while len(frontier) > 0:
            state = frontier.pop()
            closure.add(state)
            key = state, EPSILON
            if key not in transitions:
                continue
            for state in transitions[key]:
                if state in closure:
                    continue
                frontier.append(state)

        return closure

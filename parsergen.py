#!/usr/bin/env python3

"""
Parser generation functionality.
"""

__author__ = 'johnrickE'


from collections import defaultdict

from dataclasses import dataclass

from parser import *


@dataclass(frozen=True)
class Production:
    """
    A production rule in a context-free grammar.

    :param index    An integer used to identify the production.
    :param lhs      The non-terminal symbol on the LHS of the production.
    :param rhs      A tuple of symbols representing the RHS of the production.
    """
    index: int
    lhs: int
    rhs: tuple[int, ...]


@dataclass(frozen=True)
class Item:
    """
    An LR(1) item of the general form [A -> X . Y, a] where X and Y are strings
    of terminals and non-terminals (or empty strings).

    :param rule         The production rule 'A -> X Y'.
    :param cursor       The '.' position within the RHS of the rule.
    :param lookahead    The terminal symbol 'a'.
    """
    rule: Production
    cursor: int
    lookahead: int

    def has_successor(self):
        """
        Checks if the cursor position has not reached the end of the RHS of the
        production rule, i.e. the item is not of the form [A -> X ., a].

        :return True if the cursor is not at the end of the rule RHS; False otherwise.
        """
        return self.cursor < len(self.rule.rhs)
    
    def get_successor(self):
        """
        Returns an item identical to this item with the cursor position shifted one
        place to the right. In other words, given that this item is of the form
        [A -> X . B Y, a], returns the item [A -> X B . Y, a], where B is a terminal
        or non-terminal symbol.

        :return A copy of this item with the cursor incremented by 1.
        """
        return Item(self.rule, self.cursor + 1, self.lookahead)
    
    def get_locus(self):
        """
        Returns the symbol adjacent to the cursor. Given that this item is of the
        form [A -> X . B Y, a], returns the symbol B, where B is a terminal or
        non-terminal symbol.

        :return The symbol at the cursor position within the RHS of the rule.
        """
        return self.rule.rhs[self.cursor]


class ParserGenerator:
    """
    This class generates LR(1) parsing tables for a given context-free grammar.
    
    Basic usage example:

    For a context-free grammar:
    S' -> S
    S  -> C C
    C  -> c C
    C  -> d

    1. Create reduction callbacks for each production rule.
        # Example reduction callbacks that construct an abstract syntax tree.

        def r0(terms, _): # S' -> S
            return terms[0]
        
        def r1(terms, _): # S -> C C
            node = AST()
            node.add_child(terms[0])
            node.add_child(terms[1])
            return node

        def r2(terms, _): # C -> c C
            node = AST()
            node.add_child(terms[0])
            node.add_child(terms[1])
            return node
        
        def r3(terms, _): # C -> d
            node = AST()
            node.add_child(terms[0])
            return node

    2. Create an instance of TerminalSet and NonTerminalSet
        TERMINALS = TerminalSet()
        NONTERMINALS = NonTerminalSet()

    3. Add symbols to the grammar.
        S = NONTERMINALS.add()
        C = NONTERMINALS.add()
        c = TERMINALS.add()
        d = TERMINALS.add()

    4. Create a list of production rules. Note that the goal rule should always be first in the list.
        RULES = [
            (GOAL, [S], r0), # S' -> S
            (S, [C, C], r1), # S  -> C C
            (C, [c, C], r2), # C  -> c C
            (C, [d], r3)     # C  -> d
        ]

    5. Print the parsing table.
        generator = ParserGenerator(TERMINALS, NONTERMINALS, RULES)
        generator.print_table()
    
    The print_table function outputs Python code which defines the parsing table as
    well as a 'reduction lookup buffer'. These can then be used to construct a
    Parser object. This function also detects any parsing conflicts (i.e. shift/reduce or
    reduce/reduce conflicts).
    """

    def __init__(self, terminals, non_terminals, rules):
        """
        Constructs a new ParserGenerator from the specified context-free grammar.

        :terminals A TerminalSet containing all terminals in the grammar.
        :non_terminals A NonTerminalSet containing all non-terminals in the grammar.
        :rules A list containing all production rules in the grammar.
        """
        self.terminals = terminals
        self.non_terminals = non_terminals
        self.rules = []
        self.callbacks = []
        # Convert the input rules into a format usable by the parser generator.
        for i in range(0, len(rules)):
            lhs, rhs, callback = rules[i]
            self.rules.append(Production(i, lhs, tuple(rhs)))
            self.callbacks.append((lhs, len(rhs), callback.__name__))
        self.first = self.compute_first_map()
        self.table = self.generate()
    
    def print_table(self, table='TABLE', reductions='REDUCTIONS'):
        """
        Prints Python code defining the parsing table and reduction lookup buffer.
        
        :param table        The variable name of the parsing table.
        :param reductions   The variable name of the reduction lookup buffer.
        """
        
        print('======== BEGIN CODE ========')
        print('# Automatically generated parsing table')
        print('{} = {{'.format(table))
        conflicts = False
        num_entries = 0
        for position, actions in self.table.items():
            num_entries += len(actions)
            if len(actions) > 1:
                conflicts = True
                print('\n    # PARSING CONFLICT')
                for action in actions:
                    print('    {}: {}'.format(position, action))
                print()
            else:
                print('    {}: {},'.format(position, actions.pop()))
        print('}\n')
        print('# Automatically generated reduction lookup buffer')
        print('{} = ['.format(reductions))
        for callback in self.callbacks:
            lhs, n, name = callback
            print('    ({},{},{}),'.format(lhs, n, name))
        print(']')
        print('======== END CODE ========')
        print('Parsing table contains {} entries'.format(num_entries))
        if conflicts:
            print('WARNING: Parsing conflicts were detected')
        else:
            print('No conflicts detected')
    
    def simplify_table(self, table, initial_state):
        """
        The table generation algorithm returns a parsing table that represents each state as a
        frozenset of LR(1) items. However, knowledge of LR(1) items is not needed after the table
        is generated. This function assigns integer IDs to each state and returns a new table that
        represents each state using these IDs instead.

        :param table A parsing table whose states are represented as sets of LR(1) items.
        :param initial_state The initial state returned by the generate function.

        :return A more concise representation of the input table (with the initial state = 0).
        """
        state_ids = dict()
        state_ids[initial_state] = 0

        next_state_id = 1

        def get_id(state):
            nonlocal state_ids, next_state_id
            if state not in state_ids:
                state_ids[state] = next_state_id
                next_state_id += 1
            return state_ids[state]
        
        new_table = defaultdict(set)

        for (state, symbol), actions in table.items():
            position = (get_id(state), symbol)
            for action, data in actions:
                if action == SHIFT or action == GOTO:
                    new_table[position].add((action, get_id(data)))
                elif action == REDUCE or action == ACCEPT:
                    new_table[position].add((action, data))
        
        return dict(new_table)


    def generate(self):
        """
        Generates ACTION and GOTO tables for an LR(1) parser. This function assumes that the FIRST
        sets have already been computed.
        """

        rules = self.rules
        closure = self.closure
        terminals = self.terminals

        table = defaultdict(set)
        explored = set()
        frontier = []

        initial_state = closure([Item(rules[0], 0, END)])
        frontier.append(initial_state)

        while len(frontier) > 0:
            state = frontier.pop()
            if state in explored:
                continue
            explored.add(state)
            # Transition function for this state.
            # Maps symbols to a configurating set of LR(1) items (or kernel).
            # The closure of each kernel gives the next state.
            transitions = defaultdict(list)
            for item in state:
                if item.has_successor():
                    transitions[item.get_locus()].append(item.get_successor())
                else:
                    table[(state, item.lookahead)].add((ACCEPT if item.rule.lhs == GOAL else REDUCE, item.rule.index))
            for symbol, kernel in transitions.items():
                next_state = closure(kernel)
                frontier.append(next_state)
                table[(state, symbol)].add((SHIFT if symbol in terminals else GOTO, next_state))
        
        return self.simplify_table(table, initial_state)


    def closure(self, kernel):
        """
        Computes the LR(1) closure for a given configurating set of LR(1) items (i.e. a kernel).
        Note that the kernel will be empty when this function returns.

        :param kernel   The configurating set, represented as a list of Item objects.

        :return The LR(1) closure of the given kernel, as a frozenset of Item objects.
        """

        rules = self.rules
        first = self.first
        terminals = self.terminals
        non_terminals = self.non_terminals

        state = set()

        while len(kernel) > 0:
            item = kernel.pop()
            if item in state:
                continue
            state.add(item)
            if not item.has_successor():
                continue
            non_terminal = item.get_locus()
            if non_terminal not in non_terminals:
                continue

            item = item.get_successor()
            # The FOLLOW set of an LR(1) item [A -> X . B Y, a] contains all the terminals that
            # may appear directly after the symbol B.
            follow = set()
            empty = True
            while item.has_successor():
                symbol = item.get_locus()
                if symbol in terminals:
                    follow.add(symbol)
                    empty = False
                    break
                nil_not_found = True
                for terminal in first[symbol]:
                    if terminal == NIL:
                        nil_not_found = False
                    else:
                        follow.add(terminal)
                if nil_not_found:
                    empty = False
                    break
                item = item.get_successor()
            if empty:
                follow.add(item.lookahead)
            
            for rule in rules:
                if rule.lhs != non_terminal:
                    continue
                for symbol in follow:
                    kernel.append(Item(rule, 0, symbol))

        return frozenset(state)
    
    def compute_first_map(self):
        """
        Computes the FIRST set of each non-terminal in the grammar.

        :return A list of sets representing the FIRST set of each non-terminal.
        """
        terminals = self.terminals
        non_terminals = self.non_terminals
        rules = self.rules

        first = [set() for _ in range(0, len(non_terminals))]
        changed = True

        def insert(non_terminal, terminal):
            nonlocal first, changed
            if terminal not in first[non_terminal]:
                first[non_terminal].add(terminal)
                changed = True
        
        while changed:
            changed = False
            for rule in rules:
                non_terminal = rule.lhs
                empty = True
                for symbol in rule.rhs:
                    if symbol in terminals:
                        insert(non_terminal, symbol)
                        empty = False
                        break
                    nil_not_found = True
                    for terminal in first[symbol]:
                        if terminal == NIL:
                            nil_not_found = False
                        else:
                            insert(non_terminal, terminal)
                    if nil_not_found:
                        empty = False
                        break
                if empty:
                    insert(non_terminal, NIL)
        
        return first

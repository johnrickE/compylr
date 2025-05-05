#!/usr/bin/env python3

"""
Lexer generation functionality.
"""


__author__ = 'johnrickE'


from lexer import *

import regexpr


class LexerGenerator:
    """
    This class generates deterministic finite automata from sets of regular expressions.

    Basic usage example:

    1. Create a list of token specifications:
        # Each token specification is a tuple containing the terminal symbol of the token
        # (used by the parser), and a regular expression defining the token.
        TOKENS = [
            (KEYWORD, r'int'),
            (IDENTIFIER, r'[a-zA-Z_][a-zA-Z_0-9]*'),
            (NUMBER, r'[0-9]+')
        ]

    2. Print the transition table:
        generator = LexerGenerator(TOKENS)
        generator.print_dfa()
    
    The print_dfa function outputs Python code defining the transition table of the lexer
    DFA as well as the DFA's initial state. These can be used to create a Lexer object.
    """

    def __init__(self, tokens):
        """
        Constructs a new LexerGenerator from the specified list of tokens.

        :param token    A list of token specifications.
        """
        self.tokens = tokens
        self.parser = regexpr.get_parser()
        self.dfa = self.compute_dfa()
    
    def print_dfa(self, transitions='TRANSITIONS', initial_state='INITIAL_STATE', outputs='OUTPUTS'):
        """
        Prints Python code defining the transition table of the generated DFA as well as
        the initial state and state outputs.

        :param transitions      The variable name of the transition table.
        :param initial_state    The variable name of the initial state.
        :param outputs          The variable name of the state outputs dictionary.
        """
        dfa = self.dfa

        sink_states = set()
        for state in range(0, len(dfa.transitions)):
            if dfa.is_sink_state(state):
                sink_states.add(state)
        
        print('======== BEGIN CODE ========')
        print('{} = {}\n'.format(initial_state, dfa.initial_state))
        print('{} = {{'.format(transitions))
        for state in range(0, len(dfa.transitions)):
            if state in sink_states:
                continue
            for c in range(0, regexpr.NUM_CHARS):
                next_state = dfa.transitions[state][c]
                if next_state in sink_states:
                    continue
                print('    {}:{},'.format((state, c), next_state))
        print('}\n')

        print('{} = {{'.format(outputs))
        num_conflicts = 0
        for state, terminals in dfa.outputs.items():
            if len(terminals) > 1:
                num_conflicts += 1
                print('\n    # OUTPUT CONFLICT')
                for terminal in terminals:
                    print('    {}:{},'.format(state, terminal))
                print()
            else:
                terminal = terminals.pop()
                print('    {}:{},'.format(state, terminal))
        print('}')
        print('======== END CODE ========')
        print('{} conflict(s) detected.'.format(num_conflicts))
    
    def compute_dfa(self):
        """
        Computes the DFA for the lexer.

        :return A DFA that can recognise each token.
        """
        dfa = self.get_whitespace_dfa()
        for terminal, expr in self.tokens:
            dfa = dfa.union(self.parser.parse(expr, terminal))
        return dfa.minimize()
    
    def get_whitespace_dfa(self):
        """
        Returns a DFA recognising one or more whitespace characters.
        The lexer will ignore these tokens.

        :return A DFA recognising whitespace characters.
        """
        return self.parser.parse(r'[ \n\t]+', WHITESPACE)

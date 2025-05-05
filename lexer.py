#!/usr/bin/env python3

"""
Lexer functionality.
"""


__author__ = 'johnrickE'


from parser import END, LexerError


# Whitespace token that the lexer will ignore.
WHITESPACE = 0


class Lexer:
    """
    A lexical analyser (lexer), performs tokenization on a raw byte stream.
    """

    def __init__(self, transitions, initial_state, outputs, source):
        """
        Constructs a new Lexer object.

        :param transitions      The DFA transition table. This should be generated from the lexergen.LexerGenerator class.
        :param initial_state    The DFA initial state. This should be generated from the lexergen.LexerGenerator class.
        :param outputs          The state outputs dictionary. This should be generated from the lexergen.LexerGenerator class.
        :param source           The input stream of bytes to tokenize.
        """
        self.transitions = transitions
        self.initial_state = initial_state
        self.outputs = outputs
        self.source = source
        self.position = 0
    
    def lex(self):
        """
        Returns the next token in the input stream, ignoring all whitespace tokens.

        :return A tuple representing the terminal symbol and value of the token.
        """
        token = None
        while True:
            token = self.get_next_token()
            if token[0] != WHITESPACE:
                return token
    
    def get_next_token(self):
        """
        Returns the next token in the input stream.

        :return A tuple representing the terminal symbol and value of the token.
        """
        if self.position >= len(self.source):
            return END, None

        state = self.initial_state
        old_position = self.position
        new_position = old_position
        position = old_position
        lexeme = None

        if state in self.outputs:
            lexeme = self.outputs[state]
            new_position = position + 1

        for c in self.source[old_position:]:
            key = state, ord(c)
            if key not in self.transitions:
                break
            next_state = self.transitions[key]
            if next_state in self.outputs:
                lexeme = self.outputs[next_state]
                new_position = position + 1
            state = next_state
            position += 1
        
        if lexeme is None:
            raise LexerError('Invalid token')
        self.position = new_position
        return lexeme, self.source[old_position:new_position]

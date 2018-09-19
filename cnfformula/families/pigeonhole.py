#!/usr/bin/env python
# -*- coding:utf-8 -*-
"""Implementation of the pigeonhole principle formulas
"""

from cnfformula.cnf import CNF,binary_mapping,unary_mapping
from cnfformula.cmdline import BipartiteGraphHelper
from cnfformula.graphs import bipartite_sets

import cnfformula.cmdline
import cnfformula.families

from cnfformula.graphs import neighbors
from itertools import combinations,product

@cnfformula.families.register_cnf_generator
def PigeonholePrinciple(pigeons,holes,functional=False,onto=False):
    """Pigeonhole Principle CNF formula

    The pigeonhole  principle claims  that no M  pigeons can sit  in N
    pigeonholes  without collision  if M>N.   The  counterpositive CNF
    formulation  requires  such mapping  to  be  satisfied. There  are
    different  variants of this  formula, depending  on the  values of
    `functional` and `onto` argument.

    - PHP: pigeon can sit in multiple holes
    - FPHP: each pigeon sits in exactly one hole
    - onto-PHP: pigeon can  sit in multiple holes, every  hole must be
                covered.
    - Matching: one-to-one bijection between pigeons and holes.

    Arguments:
    - `pigeon`: number of pigeons
    - `hole`:   number of holes
    - `functional`: add clauses to enforce at most one hole per pigeon
    - `onto`: add clauses to enforce that any hole must have a pigeon

    >>> print(PigeonholePrinciple(4,3).dimacs(export_header=False))
    p cnf 12 22
    1 2 3 0
    4 5 6 0
    7 8 9 0
    10 11 12 0
    -1 -4 0
    -1 -7 0
    -1 -10 0
    -4 -7 0
    -4 -10 0
    -7 -10 0
    -2 -5 0
    -2 -8 0
    -2 -11 0
    -5 -8 0
    -5 -11 0
    -8 -11 0
    -3 -6 0
    -3 -9 0
    -3 -12 0
    -6 -9 0
    -6 -12 0
    -9 -12 0
    """

    def var_name(p,h):
        return 'p_{{{0},{1}}}'.format(p,h)

    if functional:
        if onto:
            formula_name="Matching"
        else:
            formula_name="Functional pigeonhole principle"
    else:
        if onto:
            formula_name="Onto pigeonhole principle"
        else:
            formula_name="Pigeonhole principle"

    php=CNF()
    php.header="{0} formula for {1} pigeons and {2} holes\n".format(formula_name,pigeons,holes)\
        + php.header

    mapping=unary_mapping(
        range(1,pigeons+1),
        range(1,holes+1),
        var_name=var_name,
        injective = True,
        functional = functional,
        surjective = onto)

    php.mode_unchecked()
    mapping.load_variables_to_formula(php)
    mapping.load_clauses_to_formula(php)
    php.mode_default()

    return php

@cnfformula.families.register_cnf_generator
def GraphPigeonholePrinciple(graph,functional=False,onto=False):
    """Graph Pigeonhole Principle CNF formula

    The graph pigeonhole principle CNF formula, defined on a bipartite
    graph G=(L,R,E), claims that there is a subset E' of the edges such that
    every vertex on the left size L has at least one incident edge in E' and
    every edge on the right side R has at most one incident edge in E'.

    This is possible only if the graph has a matching of size |L|.

    There are different variants of this formula, depending on the
    values of `functional` and `onto` argument.

    - PHP(G):  each left vertex can be incident to multiple edges in E'
    - FPHP(G): each left vertex must be incident to exaclty one edge in E'
    - onto-PHP: all right vertices must be incident to some vertex
    - matching: E' must be a perfect matching between L and R

    Arguments:
    - `graph` : bipartite graph
    - `functional`: add clauses to enforce at most one edge per left vertex
    - `onto`: add clauses to enforce that any right vertex has one incident edge


    Remark: the graph vertices must have the 'bipartite' attribute
    set. Left vertices must have it set to 0 and the right ones to
    1. A KeyException is raised otherwise.

    """

    def var_name(p,h):
        return 'p_{{{0},{1}}}'.format(p,h)

    if functional:
        if onto:
            formula_name="Graph matching"
        else:
            formula_name="Graph functional pigeonhole principle"
    else:
        if onto:
            formula_name="Graph onto pigeonhole principle"
        else:
            formula_name="Graph pigeonhole principle"


    gphp=CNF()
    gphp.header="{0} formula for graph {1}\n".format(formula_name,graph.name)

    Left, Right = bipartite_sets(graph)

    mapping = unary_mapping(Left,Right,
                            sparsity_pattern=graph,
                            var_name=var_name,
                            injective = True,
                            functional = functional,
                            surjective = onto)

    gphp.mode_unchecked()
    mapping.load_variables_to_formula(gphp)
    mapping.load_clauses_to_formula(gphp)
    gphp.mode_default()

    return gphp

@cnfformula.families.register_cnf_generator
def BinaryPigeonholePrinciple(pigeons,holes):
    """Binary Pigeonhole Principle CNF formula

    The pigeonhole principle claims that no M pigeons can sit in
    N pigeonholes without collision if M>N. This formula encodes the
    principle using binary strings to identify the holes.

    Parameters
    ----------
    pigeon : int
       number of pigeons
    holes : int
       number of holes
    """

    bphp=CNF()
    bphp.header="Binary Pigeonhole Principle for {0} pigeons and {1} holes\n".format(pigeons,holes)\
                 + bphp.header

    mapping=binary_mapping(range(1,pigeons+1),
                           range(1,holes+1), injective = True)
    bphp.mode_unchecked()
    mapping.load_variables_to_formula(bphp)
    mapping.load_clauses_to_formula(bphp)
    bphp.mode_default()

    return bphp

@cnfformula.cmdline.register_cnfgen_subcommand
class PHPCmdHelper(object):
    """Command line helper for the Pigeonhole principle CNF"""

    name='php'
    description='pigeonhole principle'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for pigeonhole principle formula

        Arguments:
        - `parser`: parser to load with options.
        """
        parser.add_argument('pigeons',metavar='<pigeons>',type=int,help="Number of pigeons")
        parser.add_argument('holes',metavar='<holes>',type=int,help="Number of holes")
        parser.add_argument('--functional',action='store_true',
                            help="pigeons sit in at most one hole")
        parser.add_argument('--onto',action='store_true',
                            help="every hole has a sitting pigeon")

    @staticmethod
    def build_cnf(args):
        """Build a PHP formula according to the arguments

        Arguments:
        - `args`: command line options
        """
        return PigeonholePrinciple(args.pigeons,
                                   args.holes,
                                   functional=args.functional,
                                   onto=args.onto)


@cnfformula.cmdline.register_cnfgen_subcommand
class GPHPCmdHelper:
    """Command line helper for the Pigeonhole principle on graphs"""

    name='gphp'
    description='graph pigeonhole principle'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for pigeonhole principle formula over graphs

        Arguments:
        - `parser`: parser to load with options.
        """
        parser.add_argument('--functional',action='store_true',
                            help="pigeons sit in at most one hole")
        parser.add_argument('--onto',action='store_true',
                            help="every hole has a sitting pigeon")
        BipartiteGraphHelper.setup_command_line(parser)


    @staticmethod
    def build_cnf(args):
        """Build a Graph PHP formula according to the arguments

        Arguments:
        - `args`: command line options
        """
        G = BipartiteGraphHelper.obtain_graph(args)
        return GraphPigeonholePrinciple(G,
                                        functional=args.functional,
                                        onto=args.onto)



@cnfformula.cmdline.register_cnfgen_subcommand
class BPHPCmdHelper(object):
    """Command line helper for the Pigeonhole principle CNF"""

    name='bphp'
    description='binary pigeonhole principle'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for pigeonhole principle formula

        Arguments:
        - `parser`: parser to load with options.
        """
        parser.add_argument('pigeons',metavar='<pigeons>',type=int,help="Number of pigeons")
        parser.add_argument('holes',metavar='<holes>',type=int,help="Number of holes")

    @staticmethod
    def build_cnf(args):
        """Build a PHP formula according to the arguments

        Arguments:
        - `args`: command line options
        """
        return BinaryPigeonholePrinciple(args.pigeons,
                                         args.holes)

@cnfformula.families.register_cnf_generator
def HiddenPigeonholePrinciple(pigeons,items,holes):
    """Hidden Pigeonhole Principle CNF formula

    Each pigeon has multiple items that should be fit into a hole, however each
    hole can only contain items of at most one pigeon.

    It is called hidden pigeon hole principle as it is only adding more
    constraints to the origianal pigeon hole principle, which makes it difficult
    to detect "the right" at-most-one constraints.

    Arguments:
    - `pigeons`: number of pigeons
    - `items`: number of items per pigeon
    - `holes`:   number of holes
    """

    def var(p,i,h):
        return 'p_{{{0},{1},{2}}}'.format(p,h,i)

    php=CNF()
    php.header="hidden pigeon hole principle formula for {0} pigeons, each having {2} items ,and {1} holes\n".format(pigeons,holes, items)\
        + php.header

    for p in range(pigeons):
        for i in range(items):
            php.add_clause([(True, var(p,i,h)) for h in range(holes)])

    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1):
                for i1 in range(items):
                    for i2 in range(items):
                        php.add_clause([(False, var(p1,i1,h)), (False, var(p2,i2,h))])

    return php


@cnfformula.cmdline.register_cnfgen_subcommand
class HPHPCmdHelper(object):
    """Command line helper for the Pigeonhole principle CNF"""

    name='hphp'
    description='hidden pigeonhole principle'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for hiden pigeonhole principle formula

        Arguments:
        - `parser`: parser to load with options.
        """
        parser.add_argument('pigeons',metavar='<pigeons>',type=int,help="Number of pigeons")
        parser.add_argument('items',metavar='<items>',type=int,help="Number of items per pigeon")
        parser.add_argument('holes',metavar='<holes>',type=int,help="Number of holes")


    @staticmethod
    def build_cnf(args):
        """Build a PHP formula according to the arguments

        Arguments:
        - `args`: command line options
        """
        return HiddenPigeonholePrinciple(args.pigeons,
                                args.items, args.holes)
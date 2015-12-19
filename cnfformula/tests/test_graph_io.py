#!/usr/bin/env python

from __future__ import unicode_literals

from io import StringIO as sio
from io import BytesIO
from six.moves import xrange

import networkx as nx
import unittest

import cnfformula
from cnfformula.graphs import readGraph,writeGraph

from . import example_filename

dot_path2 = 'graph G { 0 -- 1 -- 2}'
gml_path2 = """
        graph [
           node [
             id 0
             label 0
           ]
           node [
             id 1
             label 1
           ]
           node [
             id 2
             label 2
           ]
           edge [
             source 0
             target 1
           ]
           edge [
             source 1
             target 2
           ]
         ]"""

dimacs_path2 ="p edge 3 2\ne 1 2\ne 2 3\n"



class TestGraphIO(unittest.TestCase) :

    def check_pydot2(self):
        try:
            import pydot
            # Distinguish pydot from pydot2 from version number
            from distutils.version import StrictVersion
            pydot_version = StrictVersion(pydot.__version__)
            pydot2_version = StrictVersion("1.0.29")
            if pydot_version < pydot2_version :
                raise ImportError
        except ImportError:
            self.skipTest("PyDot2 not installed. Can't test DOT I/O")

    def test_low_level_pydot_read_path2(self) :

        self.check_pydot2()

        G = nx.Graph(nx.read_dot(sio(dot_path2)))

    def test_low_level_gml_read_path2(self) :

        # Should be a StringIO, workaround bug in NetworkX
        G = nx.read_gml(BytesIO(gml_path2.encode('ascii')))

        self.assertEqual(G.order(), 3)
        self.assertEqual(len(G.edges()), 2)
        self.assertTrue(G.has_edge(0, 1))
        self.assertTrue(G.has_edge(1, 2))
        self.assertFalse(G.has_edge(0, 2))

    def test_low_level_dimacs_read_path2(self) :

        G = cnfformula.graphs._read_graph_dimacs_format(sio(dimacs_path2))

        self.assertEqual(G.order(), 3)
        self.assertEqual(len(G.edges()), 2)
        self.assertTrue(G.has_edge(1, 2))
        self.assertTrue(G.has_edge(2, 3))
        self.assertFalse(G.has_edge(1, 3))


    def test_readGraph_dot_path2(self) :

        self.check_pydot2()

        self.assertRaises(ValueError, readGraph, sio(dot_path2), graph_type='simple')
        G = readGraph(sio(dot_path2), graph_type='simple', file_format = 'dot')
        self.assertEqual(G.order(), 3)
        self.assertEqual(len(G.edges()), 2)

    def test_readGraph_gml_path2(self) :

        self.assertRaises(ValueError, readGraph, sio(gml_path2), graph_type='simple')
        # Should be a StringIO, workaround bug in NetworkX
        G = readGraph(BytesIO(gml_path2.encode('ascii')), graph_type='simple', file_format = 'gml')
        self.assertEqual(G.order(), 3)
        self.assertEqual(len(G.edges()), 2)


    def test_readGraph_dimacs_path2(self) :

        self.assertRaises(ValueError, readGraph, sio(dimacs_path2), graph_type='simple')
        G = readGraph(sio(dimacs_path2), graph_type='simple', file_format = 'dimacs')
        self.assertEqual(G.order(), 3)
        self.assertEqual(len(G.edges()), 2)

    def test_readGraph_dot_path2_file(self) :

        self.check_pydot2()

        with open(example_filename('path2.dot'),'r') as ifile:

            # Parsing should fail here
            self.assertRaises(ValueError, readGraph, ifile, graph_type='simple', file_format='gml')

            ifile.seek(0)
            
            # Parser should guess that it is a dot file
            G = readGraph(ifile, graph_type='simple')
            self.assertEqual(G.order(), 3)
            self.assertEqual(len(G.edges()), 2)


    def test_undoable_io(self) :

        # assumes that 'does_not_exist.gml' does not exist in the working directory
        self.assertRaises(IOError, readGraph, "does_not_exist.gml", graph_type='simple')

        # assumes that '/does_not_exist.gml' is not writable
        self.assertRaises(IOError, writeGraph, nx.Graph(),"/does_not_exist.gml", graph_type='simple')


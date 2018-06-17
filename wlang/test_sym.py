# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import unittest
import wlang.ast as _ast_
import wlang.sym as _sym_
import z3

class TestSym (unittest.TestCase):

    def test_one (self):
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = _ast_.parse_string (prg1)
        sym = _sym_.SymExec ()
        st = _sym_.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)


    def test_if(self):
        prg1 = "havoc x ; if x > 10 then x := x + 1 else x := x+2 "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 2)

    def test_While_noinv1(self):
        prg1 = "havoc x; while x>5  do x:=x-1 "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 11)

    def test_While_noinv2(self):
        prg1 = "havoc x; while x<=5  do x:=x-1 "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)


    def test_While_inv(self):
        prg1 = "havoc x,y; assume y >= 0; c:= 0; r:= x; while c<y inv c <= y  and r = x + c do { r:= r+1; c:= c+1 }; assert r= x+y "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_if(self):
        prg1 = "havoc x ; if x > 10 then x := x + 1 else x := x+2 "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 2)

    def test_solver(self):
        prg1 = "havoc x; while x<=5  do x:=x-1 "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        import z3
        st = _sym_.SymState(z3.Solver())
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_3stmt_op(self):
        prg1 = "havoc x; assume x > 10; assert x < 15"
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_Bexp(self):
        prg1 = "x := -1; y := 3; if x = y or x >= y and not false then skip"
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_aexp_twoHavoc(self):
        prg1 = "havoc x, y; x := x * ( x/y - 3) + 0  ; while x > y do x := x - 1"
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 11)

    def test_aexp_twoHavoc2(self):
        prg1 = " x := 0; y := 1; if x>y+1 then x := 100"
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_bexp_skip(self):
        prg1 = "x := 0 ; y:= 0; if x=y then skip; print_state y "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_While3(self):
        prg1 = "x := 7; while x>5  do x:=x-1 "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertIsNotNone(st.to_smt2())
        self.assertEquals(len(out), 1)

    def test_assert_error(self):
        prg1 = "x:=10; y := 11; assert y = x "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_assume_error(self):
        prg1 = "x:=10; y := 11; assume y = x "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        st.is_error()
        print repr(st)
        out = [s for s in sym.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_pick_concrete(self):
        solver = z3.Solver()
        st = _sym_.SymState (solver)
        st.add_pc(z3.BoolVal(False))
        self.assertIsNone(st.pick_concerete())

    def test_While_inv2(self):
        prg1 = "havoc x,y; assume y >= 0; c:= 0; r:= x; while c<y inv c > y  and r = x + c do { r:= r+1; c:= c+1 }; assert r= x+y "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        #self.assertEquals(len(out), 1)

    def test_While_inv3(self):
        prg1 = "havoc x,y; assume y >= 0; c:= 0; r:= x; while c<y inv c <= y  and r = x + c do { r:= r+8; c:= c+1 }; assert r= x+y "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        #self.assertEquals(len(out), 1)

    def test_While_inv4(self):
        prg1 = "havoc x,y; assume y >= 0; c:= 0; r:= x; while c<y inv c <= y  and r = x + c do { r:= r+1; c:= c+1 }; assert r= x+2*y "
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        # self.assertEquals(len(out), 1)

    def test_While_inv5(self):
        prg1 = "havoc x,y; assume y >= 0; c:= 0; r:= x; while true inv c <= y  and r = x + c do { r:= r+1; c:= c+1 }; assert r= x+y"
        ast1 = _ast_.parse_string(prg1)
        sym = _sym_.SymExec()
        st = _sym_.SymState()
        out = [s for s in sym.run(ast1, st)]
        # self.assertEquals(len(out), 1)






/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

This is just a trick to embed the 'tactic language' as a Lean
expression. We should view 'tactic' as automation that when execute
produces a term.  tactic.builtin is just a "dummy" for creating the
definitions that are actually implemented in C++
-/
prelude
import init.datatypes init.reserved_notation init.num

inductive tactic :
Type _ := builtin : tactic

namespace tactic
-- Remark the following names are not arbitrary, the tactic module
-- uses them when converting Lean expressions into actual tactic objects.
-- The bultin 'by' construct triggers the process of converting a
-- a term of type 'tactic' into a tactic that sythesizes a term
@[hott] def and_then    (t1 t2 : tactic) : tactic := builtin
@[hott] def or_else     (t1 t2 : tactic) : tactic := builtin
@[hott] def par         (t1 t2 : tactic) : tactic := builtin
@[hott] def fixpoint    (f : tactic → tactic) : tactic := builtin
@[hott] def repeat      (t : tactic) : tactic := builtin
@[hott] def at_most     (t : tactic) (k : num)  : tactic := builtin
@[hott] def discard     (t : tactic) (k : num)  : tactic := builtin
@[hott] def focus_at    (t : tactic) (i : num)  : tactic := builtin
@[hott] def try_for     (t : tactic) (ms : num) : tactic := builtin
@[hott] def all_goals   (t : tactic) : tactic := builtin
@[hott] def now         : tactic := builtin
@[hott] def assumption  : tactic := builtin
@[hott] def eassumption : tactic := builtin
@[hott] def state       : tactic := builtin
@[hott] def fail        : tactic := builtin
@[hott] def id          : tactic := builtin
@[hott] def beta        : tactic := builtin
@[hott] def info        : tactic := builtin
@[hott] def whnf        : tactic := builtin
@[hott] def contradiction : tactic := builtin
@[hott] def exfalso     : tactic := builtin
@[hott] def congruence  : tactic := builtin
@[hott] def rotate_left (k : num) := builtin
@[hott] def rotate_right (k : num) := builtin
@[hott] def rotate (k : num) := rotate_left k

-- This is just a trick to embed expressions into tactics.
-- The nested expressions are "raw". They tactic should
-- elaborate them when it is executed.
inductive expr : Type _ :=
builtin : expr

inductive expr_list : Type _ :=
| nil  : expr_list
| cons : expr → expr_list → expr_list

-- auxiliary type used to mark optional list of arguments
@[hott] def opt_expr_list := expr_list

-- auxiliary types used to mark that the expression is suppose to be an identifier, optional, or a list.
@[hott] def identifier := expr
@[hott] def identifier_list := expr_list
@[hott] def opt_identifier_list := expr_list
-- Remark: the parser has special support for tactics containing `location` parameters.
-- It will parse the optional `at ...` modifier.
@[hott] def location := expr
-- Marker for instructing the parser to parse it as 'with <expr>'
@[hott] def with_expr := expr

-- Marker for instructing the parser to parse it as '?(using <expr>)'
@[hott] def using_expr := expr
-- Constant used to denote the case were no expression was provided
@[hott] def none_expr : expr := expr.builtin

@[hott] def apply      (e : expr)            : tactic := builtin
@[hott] def eapply     (e : expr)            : tactic := builtin
@[hott] def fapply     (e : expr)            : tactic := builtin
@[hott] def rename     (a b : identifier)    : tactic := builtin
@[hott] def intros      (e : opt_identifier_list) : tactic := builtin
@[hott] def generalize_tac (e : expr) (id : identifier) : tactic := builtin
@[hott] def clear      (e : identifier_list) : tactic := builtin
@[hott] def revert     (e : identifier_list) : tactic := builtin
@[hott] def refine     (e : expr)            : tactic := builtin
@[hott] def exact      (e : expr)            : tactic := builtin
-- Relaxed version of exact that does not enforce goal type
@[hott] def rexact     (e : expr)            : tactic := builtin
@[hott] def check_expr (e : expr)            : tactic := builtin
@[hott] def trace      (s : string)          : tactic := builtin

-- rewrite_tac is just a marker for the builtin 'rewrite' notation
-- used to create instances of this tactic.
@[hott] def rewrite_tac  (e : expr_list) : tactic := builtin
@[hott] def xrewrite_tac (e : expr_list) : tactic := builtin
@[hott] def krewrite_tac (e : expr_list) : tactic := builtin
@[hott] def replace (old : expr) (new : with_expr) (loc : location) : tactic := builtin

-- Arguments:
--  - ls : lemmas to be used (if not provided, then blast will choose them)
--  - ds : definitions that can be unfolded (if not provided, then blast will choose them)
@[hott] def blast (ls : opt_identifier_list) (ds : opt_identifier_list) : tactic := builtin

-- with_options_tac is just a marker for the builtin 'with_options' notation
@[hott] def with_options_tac (o : expr) (t : tactic) : tactic := builtin
-- with_options_tac is just a marker for the builtin 'with_attributes' notation
@[hott] def with_attributes_tac (o : expr) (n : identifier_list) (t : tactic) : tactic := builtin

@[hott] def cases (h : expr) (ids : opt_identifier_list) : tactic := builtin

@[hott] def induction (h : expr) (rec : using_expr) (ids : opt_identifier_list) : tactic := builtin

@[hott] def intros (ids : opt_identifier_list) : tactic := builtin

@[hott] def generalizes (es : expr_list) : tactic := builtin

@[hott] def clears  (ids : identifier_list) : tactic := builtin

@[hott] def reverts (ids : identifier_list) : tactic := builtin

@[hott] def change (e : expr) : tactic := builtin

@[hott] def assert_hypothesis (id : identifier) (e : expr) : tactic := builtin

@[hott] def note_tac (id : identifier) (e : expr) : tactic := builtin

@[hott] def constructor (k : option num)  : tactic := builtin
@[hott] def fconstructor (k : option num) : tactic := builtin
@[hott] def existsi (e : expr)            : tactic := builtin
@[hott] def split                         : tactic := builtin
@[hott] def left                          : tactic := builtin
@[hott] def right                         : tactic := builtin

@[hott] def injection (e : expr) (ids : opt_identifier_list) : tactic := builtin

@[hott] def subst (ids : identifier_list) : tactic := builtin
@[hott] def substvars : tactic := builtin

@[hott] def reflexivity             : tactic := builtin
@[hott] def symmetry                : tactic := builtin
@[hott] def transitivity (e : expr) : tactic := builtin

@[hott] def try         (t : tactic) : tactic := or_else t id
@[hott] def repeat1     (t : tactic) : tactic := and_then t (repeat t)
@[hott] def focus       (t : tactic) : tactic := focus_at t 0
@[hott] def determ      (t : tactic) : tactic := at_most t 1
@[hott] def trivial                  : tactic := or_else (apply eq.refl) assumption
@[hott] def do (n : nat) (t : tactic) : tactic :=
nat.rec id (λn t', and_then t t') n

end tactic
tactic_infixl `;`:15 := tactic.and_then
tactic_notation T1 `:`:15 T2 := tactic.focus (tactic.and_then T1 (tactic.all_goals T2))
tactic_notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` := r

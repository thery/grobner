[![Build Status](https://travis-ci.org/thery/grobner.svg?branch=master)](https://travis-ci.org/thery/grobner)

# grobner
A fornalisation of Grobner basis in ssreflect.
It contains one file

``grobner.v``

It defines

```coq
From mathcomp Require Import all_ssreflect all_algebra.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.
From mathcomp.contrib.grobner Require Import grobner.

Print ideal.

(*
ideal =
fun (R : ringType) (n : nat) (L : seq {mpoly R[n]}) (p : {mpoly R[n]})
  =>
  exists t, p = \sum_(i < size L) t`_i * L`_i
*)

(* it is decidable *)

Check idealfP.

(*
idealfP
     : forall (R : fieldType)  (n : nat) (p : {mpoly R[n]})
              (l : seq {mpoly R[n]}),
       reflect (ideal l p) (idealf l p)
*)
```

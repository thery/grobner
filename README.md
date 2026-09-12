<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Grobner

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/grobner/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/grobner/actions/workflows/docker-action.yml




A fornalisation of Grobner basis in ssreflect.
It contains one file

``grobner.v``

It defines

```rocq
From mathcomp Require Import boot algebra.
From mathcomp Require Import ssrcomplements freeg mpoly.
From mathcomp.contrib.grobner Require Import grobner.

Print ideal.

(*
ideal =
fun (R : ringType) (n : nat) (L : seq {mpoly R[n]}) (p : {mpoly R[n]})
  =>
  exists t, p = sum_(i < size L) t`_i * L`_i
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

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [MathComp ssreflect 2.6 or later](https://math-comp.github.io)
  - [MathComp algebra 2.6 or later](https://math-comp.github.io)
  - [MathComp Multinomials 2.5 or later](https://github.com/math-comp/multinomials)
- Rocq/Coq namespace: `grobner`
- Related publication(s): none

## Building and installation instructions

To build and install manually:

``` shell
git clone https://github.com/thery/grobner.git
cd grobner
make   # or make -j <number-of-cores-on-your-machine> 
make install
```




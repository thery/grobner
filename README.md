<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Grobner

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/grobner/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/grobner/actions?query=workflow:"Docker%20CI"




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

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.15 or later
- Additional dependencies:
  - [MathComp ssreflect 1.15 or later](https://math-comp.github.io)
  - [MathComp algebra 1.15 or later](https://math-comp.github.io)
  - [MathComp Multinomials 1.5.5 or later](https://github.com/math-comp/multinomials)
- Coq namespace: `grobner`
- Related publication(s): none

## Building and installation instructions

``` shell
git clone https://github.com/thery/grobner.git
cd grobner
make   # or make -j <number-of-cores-on-your-machine> 
make install
```




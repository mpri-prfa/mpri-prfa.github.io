(** MPRI PRFA 2024 Test file

  This test file should run perfectly if you have Coq 8.18.0 installed as well
  as the required Equations and MetaCoq version.

  You only need to make sure you can interpret the whole file, not understand
  it.

**)

(* This should test that you have Coq installed *)
From Coq Require Import Lia.

(* This should test that you also have Equations *)
From Equations Require Import Equations.

(* And MetaCoq *)
From MetaCoq.Template Require Import All.

(* Testing new feature of 8.18 *)
#[deprecated(note="not really")] Definition foo := 1.

(* Testing Equations *)

Equations eq_test (x : bool) : nat :=
  eq_test true := 12 ;
  eq_test false := 1.

(* Testing MetaCoq *)

MetaCoq Quote Definition eq_test_term := eq_test.
Print eq_test_term.

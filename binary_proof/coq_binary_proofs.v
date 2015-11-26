Require Import Omega Coq.Arith.Plus Coq.Arith.Mult Lists.List.
Import ListNotations.

(***********************************************************************)
(*                                                                     *)
(*                            ASSIGNMENT                               *)
(*                                                                     *)
(***********************************************************************)

(***********************************************************************)
(*                            1. SETUP                                 *)
(***********************************************************************)
(* 
 
To complete this assignment you must first download and install Coq.
You can download Coq from https://coq.inria.fr/download
Please download the current version "Coq 8.4". I suggest downloading a
version that is bundled with CoqIDE as it will simplify getting started,
but if you're familiar with Emacs, ProofGeneral is a good option.

*)



(***********************************************************************)
(*                            2. NOTES                                 *)
(***********************************************************************)

(* These are the functions we defined in class on Wednesday and the    *)
(* corresponding theorems we proved. This will hopefully serve as a    *)
(* refresher on how to write functions and prove theorems in Coq.      *)



(* `Fixpoint` allows the definition of recursive functions in Coq      *)
(* It is similar to Racket's `define`                                  *)
(* Most functions written in Coq will make use of pattern matching     *)
(* using the syntax below. All possible cases must be covered or Coq   *)
(* will reject the definition. Furthermore, Coq must be able to prove  *)
(* that a function will terminate, often this is done by ensuring      *)
(* that each recursive call to a function operates on a structurally   *)
(* smaller piece of the input. In the definition below, `to_nat` takes *)
(* the list `bs` as an argument, but only recurs on the tail of the    *)
(* list.                                                               *)
Fixpoint to_nat (bs : list bool) : nat :=
  match bs with
    | [] => 0
    | b :: bs_tail =>
      match b with
        | true =>  2*to_nat bs_tail + 1
        | false => 2*to_nat bs_tail
      end
  end.

(* The `Theorem` keyword indicates to Coq that we are stating and      *)
(* proving a theorem. We will use this syntax to write test cases for  *)
(* our function definitions. Test cases are just simple theorems which *)
(* can usually be proved by performing computation.                    *)
(*                                                                     *)
(* Proofs in Coq begin with the `Proof` keyword and end with `Qed` to  *)
(* indicate that a proof has been completed and register that the      *)
(* proof has been defined.                                             *)
(*                                                                     *)
(* When proving theorems in Coq, the system presents us a `goal` in    *)
(* the form of a proof tree that looks something like the following:   *)
(*
  ============================
   to_nat [] = 0
 *)
(* Proofs in Coq take the form of a list of commands called `tactics`. *)
(* Each tactic modifies the current goal or subgoal in a specific way. *)
(* To solve the above goal, for example, we can use the `compute`      *)
(* tactic to evaluate the result of `to_nat []`, this replaces the     *)
(* goal above with:                                                    *)
(*
  ============================
   0 = 0
 *)
(* Now we can be confident that the theorem we are trying to prove is  *)
(* actually true. To solve any goal of the ` X = X,` where `X` is any  *)
(* arbitrary expression, we will use the tactic `reflexivity`.         *)
(* Using reflexivity on the above goal solves it immediately and       *)
(* and leaves no additional subgoals. The proof is complete, to signal *)
(* to Coq that we are finished we write `Qed`.                         *)

Theorem to_nat_ex1 : to_nat [] = 0.
Proof.
  compute.
  reflexivity.
Qed.

Theorem to_nat_ex2 : to_nat [true;false] = 1.
Proof.
  compute.
  reflexivity.
Qed.

Theorem to_nat_ex3 : to_nat [true;false;true;true] = 13.
Proof.
  compute.
  reflexivity.
Qed.

Fixpoint add1_b (bs : list bool) : list bool :=
  match bs with
    | [] => [true]
    | b :: bs_tail =>
      match b with
        | true => false :: add1_b  bs_tail
        | false => true :: bs_tail
      end
  end.

Theorem add1_ex1 : add1_b [] = [true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem add1_ex2 : add1_b [true;true] = [false;false;true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem add1_ex3 : add1_b [false;true] = [true;true].
Proof.
  compute.
  reflexivity.
Qed.

(* The first interesting theorem we will prove is that the add1        *)
(* procedure  on our representation of binary numbers performs the     *) 
(* same operation as adding 1 to the natural number representation.    *)
(* After stating the theorem we have the following goal to prove:      *)
(*
============================
 forall bs : list bool, to_nat (add1_b bs) = to_nat bs + 1
*)
(* As with any `forall` quantified proof, in order to prove such a     *)
(* theorem we must first obtain an instance of `bs`. In Coq, the       *)
(* `intro` tactic followed by the name of the variable performs this   *)
(* task. The `intro bs` tactic will modify the current goal giving:    *)     
(*
 bs : list bool
  ============================
   to_nat (add1_b bs) = to_nat bs + 1
*)
(* In general, the goals that Coq presents us with will contain the   *)
(* facts we know to be true above the "bar" and the goal or statement  *)
(* we are trying to prove below it. In this case we only know that `bs`*)
(* has the type `list bool` and from that we wish to prove that        *)
(* `to_nat (add1_b bs) = to_nat bs + 1` holds.                         *)
(* To prove this statement we will perform induction on the variable   *)
(* `bs`. Unsurprisingly the tactic for performing induction is         *)
(* `induction` followed by the name of the variable we are inducting   *)
(* over.                                                               *)
(* Since we are inducting over a list of booleans, using this tactic   *)
(* will replace the current goal with 2 new subgoals, one for each of  *)
(* the possible representations of a list. More specifically, we need  *)
(* to show that `to_nat (add1_b bs) = to_nat bs + 1` will hold when    *)
(* `bs` is the empty list, `[]`, and also when `bs` has the form       *)
(* `a :: bs` for some boolean value `a`. Analagous to induction over   *)
(* the natural numbers we have a base case and an inductive case as    *)
(* described above. In the inductive case, Coq generates the inductive *)
(* hypothesis for us and adds it to out list of facts.                 *)
(* After using induction we have the following proof state:            *)
(*
  ============================
   to_nat (add1_b []) = to_nat [] + 1

subgoal 2 (ID 64) is:
 to_nat (add1_b (a :: bs)) = to_nat (a :: bs) + 1
*)
(* As we have done for the test cases above, we can easily solve the   *)
(* first goal by using the `compute` and `reflexivity` tactics in      *)
(* in order. This leaves us with the remaining second goal:            *)
(*
  a : bool
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat (add1_b (a :: bs)) = to_nat (a :: bs) + 1
*)
(* We can see that Coq has added an inductive hypothesis with the name *)
(* `IHbs` to our list of facts. Now we get stuck using only the        *)
(* tactics introduced so far. Trying to use `compute` will change the  *)
(* goal, but not in any way that helps. The `compute` tactic performs  *)
(* as much evaluation as it can, but without concrete values for `a`   *)
(* it will even reduce our `Fixpoint` definitions to a more primitive  *)
(* form that is both difficult to read and challenging to prove        *)
(* theorems about. Instead we need to know something about the value   *)
(* `a`. To do this we use the `destruct` tactic which allows us to     *)
(* consider all the possible forms a value may take. For a boolean     *)
(* such as `a` we will consider the cases where `a` is true and where  *)
(* `a` is false. The `destruct` tactic will replace the currect goal   *)
(* with new subgoals for each possible form of the destruced value.    *)
(* Here, using `destruct a` gives the new proof state:                 *)
(*
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat (add1_b (true :: bs)) = to_nat (true :: bs) + 1

subgoal 2 (ID 70) is:
 to_nat (add1_b (false :: bs)) = to_nat (false :: bs) + 1
*)
(* Now we can make progress! Again we could try to use `compute` to    *)
(* solve the current goal, but we've seen how `compute` can do more    *)
(* than we expect. Instead let's use a tactic called `simpl` that      *)
(* will still evaluate, but will keep the goal in                      *)
(* roughly the same shape. The `simpl` tactic may be used on its own,  *)
(* in which case it will simplify wherever it can, or we may use it as *)
(* in `simpl add1_b` which will only simplify the `add1_b` expressions *)
(* in the current goal. This leaves us with:                           *)
(*
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat (false :: add1_b bs) = to_nat (true :: bs) + 1
*)
(* Repeating this process to simplify `to_nat` gives:                  *)
(*
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat (add1_b bs) + (to_nat (add1_b bs) + 0) =
   to_nat bs + (to_nat bs + 0) + 1 + 1
*)
(* Notice that we now have terms of the form `to_nat (add1_b bs)`.     *)
(* This is precisely the term to which our inductive hypothesis        *)
(* applies. To use our inductive hypothesis we will use the `rewrite`  *)
(* tactic. This tactic uses equations of the form `A=B` to transform   *)
(* instances of term A in the current goal into instances of term B.   *)
(* Our equations will always have names, in this case it is IHbs we    *)
(* wish to use, but note that the theorem we are proving also has this *)
(* form. If we later wish to use this theorem to rewrite a term, we    *)
(* would write `rewrite add1_correct`.                                 *)
(* Using `rewrite IHbs` here gives the new goal:                       *)
(*
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat bs + 1 + (to_nat bs + 1 + 0) =
   to_nat bs + (to_nat bs + 0) + 1 + 1
*)
(* The rewrite tactic can also be used to turn B terms into A terms,  *)
(* we would write `rewrite <- IHbs` instead, but since there were no  *)
(* instances of `to_nat bs + 1` in our goal this tactic would have    *)
(* failed.                                                            *)
(* Back to the above goal, we now have an equality that seems obvious *)
(* according to basic arithmetic. In Coq we will use the `omega`      *)
(* tactic to solve these sorts of goals. `omega` is a decision        *)
(* procedure for Presburger Arithmetic, which includes any expression *)
(* that involves only natural numbers, equality, inequality, and      *)
(* addition. Presburger arithmetic does not deal with multiplication, *)
(* though it can solve goals involving multiplication by a constant   *)
(* because these multiplications may be replaced with equivalent      *)
(* addition expressions. Using `omega` here solves the current goal   *)
(* leaving us with the remaning subgoal:                              *)
(*
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat (add1_b (false :: bs)) = to_nat (false :: bs) + 1
 *)
(* Here we will follow the same process above using the tactic         *)
(* `simpl add1_b` followed by `simpl to_nat` to reach:                 *)
(*
  bs : list bool
  IHbs : to_nat (add1_b bs) = to_nat bs + 1
  ============================
   to_nat bs + (to_nat bs + 0) + 1 = to_nat bs + (to_nat bs + 0) + 1
*)
(* Again we reach a straightforward equality. In fact, here we can     *)    
(* just use reflexivity because the goal has the form `X = X`.         *)
(* Using reflexivity immediately solves the goal and we have           *)
(* completed the proof that `add1_b` behaves correctly.                *)

Theorem add1_correct :
  forall bs, to_nat (add1_b bs) = to_nat bs + 1.
Proof.
  intro bs.
  induction bs.
  compute.
  reflexivity.
  destruct a.
  simpl add1_b.
  simpl to_nat.
  rewrite IHbs.
  omega.
  simpl add1_b.
  simpl to_nat.
  reflexivity.
Qed.

Fixpoint plus_b (b1s b2s : list bool) : list bool :=
  match b1s with
    | [] => b2s
    | b1 :: b1s_tail =>
      match b2s with
        | [] => b1s
        | b2 :: b2s_tail =>
          match b1, b2 with
            | true, true =>
              false :: add1_b (plus_b b1s_tail b2s_tail)
            | true, false =>
              true :: (plus_b b1s_tail b2s_tail)
            | false, true =>
              true :: (plus_b b1s_tail b2s_tail)
            | false, false =>
              false :: (plus_b b1s_tail b2s_tail)
          end
      end
  end.
                   

Theorem plus_ex1 : plus_b [] [] = [].
Proof.
  compute.
  reflexivity.
Qed.

Theorem plus_ex2 :
  plus_b [false;true] [true;true] = [true;false;true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem plus_ex3 :
  plus_b [true;true;false;true] [true;false; false;true]
  =
  [false; false;true;false;true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem plus_ex4 :
  plus_b [true;false] [true] = [false ;true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem plus_correct :
  forall b1 b2,
    to_nat (plus_b b1 b2) = to_nat b1 + to_nat b2.
Proof.
  intro b1.
  induction b1.
  intro b2.
  simpl.
  reflexivity.

  intro b2.
  destruct a.
  destruct b2.
  simpl.
  omega.
  destruct b.
  simpl plus_b.
  simpl to_nat.
  rewrite add1_correct.
  rewrite IHb1.
  omega.
  simpl.
  rewrite IHb1.
  omega.

  destruct b2.
  simpl.
  omega.
  destruct b.
  simpl.
  rewrite IHb1.
  omega.
  simpl.
  rewrite IHb1.
  omega.
Qed.

(* Note the change to this definition from what we did in class!       *)
(* The argument order to plus_b has been switched, this change will    *)
(* simplify the proof of correctness.                                  *)
Fixpoint mult_b (b1s b2s : list bool) : list bool :=
  match b1s with
    | [] =>  []
    | b1 :: b1s_tail =>
      match b1 with
        | true => plus_b b2s (false::mult_b b1s_tail b2s)
        | false => false :: mult_b b1s_tail b2s
      end
  end.


Theorem m_ex1 : mult_b [] [true;true] = [].
Proof.
  reflexivity.
Qed.

Theorem m_ex2 : mult_b [false;true] [true;true]
                = [false;true; true].
Proof.
  compute.
  reflexivity.
Qed.


(***********************************************************************)
(*                           3. EXERCISES                              *)
(***********************************************************************)

(* 

In class we defined functions that perform arithmetic on binary numbers 
represented as lists of booleans. In this assignment, you will prove
additional properties of the operations defined above and extend this 
library with two additional functions

 *)

(* 
Exercise 1: A Theorem About Multiplication                          
Prove the following correctness theorem about our definition of     
multiplication.

You may find the following theorems from Coq's multiplication
library helpful in proving mult_correct:

Theorem mult_plus_distr_r : forall n m p, (n + m) * p = n * p + m * p.

Theorem mult_plus_distr_l : forall n m p, n * (m + p) = n * m + n * p.
*)

Theorem mult_correct :
  forall b1 b2, to_nat (mult_b b1 b2) = to_nat b1 * to_nat b2.
Proof.
Qed.


(* 
Exercise 2: Binary addition is commutative
Prove that our plus_b function is commutative
 *)

Theorem plus_commutative :
  forall b1 b2, plus_b b1 b2 = plus_b b2 b1.
Proof.
Qed.


(* 
We would like to prove that our plus_b function is also associative.
In order to prove this fact you will need to first prove the following
theorem that relates plus_b and add1_b.
*)

(* 
Exercise 3: add1 commutes with plus
*)

Theorem add1_commutes_with_plus :
  forall b1 b2, plus_b (add1_b b1) b2 = add1_b (plus_b b1 b2).
Proof.
Qed.

(*
Exercise 4: Binary addition is associative
*)

Theorem plus_b_associative :
  forall b1 b2 b3, plus_b b1 (plus_b b2 b3) = plus_b (plus_b b1 b2) b3.
Proof.
Qed.


(* 

Extend our binary number arithmetic library to include other
functions: subtraction by one and (something like) logarithm.

Exercise 5: Define sub1_b.

Write a definition for the function sub1_b in Coq using the Fixpoint
form. The result of calling sub_1 on any representation of 0 should
also represent 0.

Exercise 6: Define log_b.

This function should return the base2 log of a number or, more
precisely, it should return the same answer as this function (except
that this function has imprecision due to floating point arithmetic):

(define (log_b n)
   (+ 1 (floor (/ (log n) (log 2)))))

The Racket function `integer-length` computes the correct answers in
an exact manner, so use the above to give you a sense of what the
right answers are and use `integer-length` if you want to check on
some (large) values.

For both 5 and 6, a correct solution satisfies the test cases at the
end of this file and not be longer than about 10 lines, give or take.

*)


(***********************************************************************)
(*                 TEST CASES FOR `sub1_b` AND `log_b`                 *)
(***********************************************************************)

Theorem sub1_b_ex0 : sub1_b [] = [].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex1 : sub1_b [true] = [false].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex2 : sub1_b [false; true] = [true; false].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex3 : sub1_b [true; true] = [false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex4 : sub1_b [false; false; true] = [true; true; false].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex5 : sub1_b [true; false; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex6 : sub1_b [false; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex7 : sub1_b [true; true; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex8 : sub1_b [false; false; false; true] = [true; true; true; false].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex9 : sub1_b [true; false; false; true] = [false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex10 : sub1_b [false; true; false; true] = [true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex11 : sub1_b [true; true; false; true] = [false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex12 : sub1_b [false; false; true; true] = [true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex13 : sub1_b [true; false; true; true] = [false; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex14 : sub1_b [false; true; true; true] = [true; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex15 : sub1_b [true; true; true; true] = [false; true; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex16 : sub1_b [false; false; false; false; true] = [true; true; true; true; false].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex17 : sub1_b [true; false; false; false; true] = [false; false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex18 : sub1_b [false; true; false; false; true] = [true; false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex19 : sub1_b [true; true; false; false; true] = [false; true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex20 : sub1_b [false; false; true; false; true] = [true; true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex21 : sub1_b [true; false; true; false; true] = [false; false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex22 : sub1_b [false; true; true; false; true] = [true; false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex23 : sub1_b [true; true; true; false; true] = [false; true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex24 : sub1_b [false; false; false; true; true] = [true; true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex25 : sub1_b [true; false; false; true; true] = [false; false; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex26 : sub1_b [false; true; false; true; true] = [true; false; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex27 : sub1_b [true; true; false; true; true] = [false; true; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex28 : sub1_b [false; false; true; true; true] = [true; true; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex29 : sub1_b [true; false; true; true; true] = [false; false; true; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex30 : sub1_b [false; true; true; true; true] = [true; false; true; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex31 : sub1_b [true; true; true; true; true] = [false; true; true; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex32 : sub1_b [false; false; false; false; false; true] = [true; true; true; true; true; false].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex33 : sub1_b [true; false; false; false; false; true] = [false; false; false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex34 : sub1_b [false; true; false; false; false; true] = [true; false; false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex35 : sub1_b [true; true; false; false; false; true] = [false; true; false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex36 : sub1_b [false; false; true; false; false; true] = [true; true; false; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex37 : sub1_b [true; false; true; false; false; true] = [false; false; true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex38 : sub1_b [false; true; true; false; false; true] = [true; false; true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex39 : sub1_b [true; true; true; false; false; true] = [false; true; true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex40 : sub1_b [false; false; false; true; false; true] = [true; true; true; false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex41 : sub1_b [true; false; false; true; false; true] = [false; false; false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex42 : sub1_b [false; true; false; true; false; true] = [true; false; false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex43 : sub1_b [true; true; false; true; false; true] = [false; true; false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex44 : sub1_b [false; false; true; true; false; true] = [true; true; false; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex45 : sub1_b [true; false; true; true; false; true] = [false; false; true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex46 : sub1_b [false; true; true; true; false; true] = [true; false; true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex47 : sub1_b [true; true; true; true; false; true] = [false; true; true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex48 : sub1_b [false; false; false; false; true; true] = [true; true; true; true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex49 : sub1_b [true; false; false; false; true; true] = [false; false; false; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex50 : sub1_b [false; true; false; false; true; true] = [true; false; false; false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem sub1_b_ex51 : to_nat (sub1_b [false; false; false; false]) = 0.
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex0 : log_b [] = [].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex1 : log_b [true] = [true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex2 : log_b [false; true] = [false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex3 : log_b [true; true] = [false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex4 : log_b [false; false; true] = [true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex5 : log_b [true; false; true] = [true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex6 : log_b [false; true; true] = [true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex7 : log_b [true; true; true] = [true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex8 : log_b [false; false; false; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex9 : log_b [true; false; false; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex10 : log_b [false; true; false; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex11 : log_b [true; true; false; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex12 : log_b [false; false; true; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex13 : log_b [true; false; true; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex14 : log_b [false; true; true; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex15 : log_b [true; true; true; true] = [false; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex16 : log_b [false; false; false; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex17 : log_b [true; false; false; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex18 : log_b [false; true; false; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex19 : log_b [true; true; false; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex20 : log_b [false; false; true; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex21 : log_b [true; false; true; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex22 : log_b [false; true; true; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex23 : log_b [true; true; true; false; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex24 : log_b [false; false; false; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex25 : log_b [true; false; false; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex26 : log_b [false; true; false; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex27 : log_b [true; true; false; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex28 : log_b [false; false; true; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex29 : log_b [true; false; true; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex30 : log_b [false; true; true; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex31 : log_b [true; true; true; true; true] = [true; false; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex32 : log_b [false; false; false; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex33 : log_b [true; false; false; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex34 : log_b [false; true; false; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex35 : log_b [true; true; false; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex36 : log_b [false; false; true; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex37 : log_b [true; false; true; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex38 : log_b [false; true; true; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex39 : log_b [true; true; true; false; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex40 : log_b [false; false; false; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex41 : log_b [true; false; false; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex42 : log_b [false; true; false; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex43 : log_b [true; true; false; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex44 : log_b [false; false; true; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex45 : log_b [true; false; true; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex46 : log_b [false; true; true; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex47 : log_b [true; true; true; true; false; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex48 : log_b [false; false; false; false; true; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex49 : log_b [true; false; false; false; true; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex50 : log_b [false; true; false; false; true; true] = [false; true; true].
Proof.
  compute.
  reflexivity.
Qed.

Theorem log_b_ex51 : to_nat (log_b [false; false; false; false]) = 0.
Proof.
  compute.
  reflexivity.
Qed.

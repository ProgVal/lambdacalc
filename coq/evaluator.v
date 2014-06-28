Require Import String.
Require Import List.
Open Scope string_scope.

(****** Types ******)

Definition var_name := string.

Definition generic_context {term : Type} : Type := term -> term
.


Inductive term : Type :=
| Var : var_name -> term
| Abs : var_name -> term -> term
| App : term -> term -> term
| Bottom : string -> term -> term
.

Definition context : Type := @generic_context term.

Implicit Type c : context.
Implicit Type t : term.
Implicit Type name : var_name.



Definition eval_cont c t cont : term :=
    match c with runs =>
        cont (runs t)
    end
.

Definition eval_cont_terminate c t :=
    eval_cont c t (fun t => t)
.


Fixpoint subst name t body :=
    match body with
    | Var v => if (string_dec v name) then t else Var v
    | Abs arg body => if (string_dec arg name) then Abs arg body else Abs arg (subst name t body)
    | App left_ right_ => App (subst name t left_) (subst name t right_)
    | Bottom r t => Bottom r t
    end
.

(***** Evaluation ******)

Definition eval_var c name : term :=
    Var name
.

Definition eval_abs c arg body : term:=
    Abs arg body
.

Definition apply c left right : term :=
    match left with
    | Abs arg body => subst arg right body
    | Bottom r t => Bottom r t
    | _ => Bottom "Apply to non-abstraction" left
    end
.

Definition eval_app c left right :=
    match left with
    | Var name => eval_var c name
    | Abs arg body => eval_cont c right (fun t => apply c left t)
    | App left_ right_ => eval_cont c (App left_ right_) (fun t => apply c t right)
    | Bottom r t => Bottom r t
    end
.

Definition eval c t : term :=
    let t := (
        match t with
        | Var name => eval_var c name
        | Abs arg body => eval_abs c arg body
        | App left_ right_ => eval_app c left_ right_
        | Bottom r t => Bottom r t
        end)
    in
    match t with
    | App left_ right_ => eval_cont_terminate c t
    | _ => t
    end
.


Fixpoint runs (max_steps : nat) t : term :=
    match max_steps with
    | 0 => Bottom "Coq is not Turing-complete" t
    | S max_steps' => eval (runs max_steps') t
    end
.

Definition call_runs t : term :=
    runs 1000 t
.

Eval vm_compute in (call_runs (App (Abs "y" (Var "y")) (Var "z"))).
Eval vm_compute in (call_runs      (App (Abs "x" (Abs "y" (Var "y"))) (Var "z1"))).
Eval vm_compute in (call_runs (App (App (Abs "x" (Abs "y" (Var "y"))) (Var "z1")) (Var "z2"))).
Eval vm_compute in (call_runs (App (Abs "x" (App (Var "x") (Var "x"))) (Abs "y" (App (Var "y") (Var "y"))))).

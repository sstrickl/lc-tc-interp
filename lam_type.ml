type id = string

(* op := + | - | * | / *)
type binop = Plus | Minus | Times | Div

(* τ := int | τ → τ *)
type typ = Int
         | Fun of typ * typ

(* Γ := · | Γ, x:τ *)
type env = (id * typ) list

(* e := e e | λx.e | e op e | x | n *)
type expr = App of expr * expr
          | Lam of id * typ * expr
          | Binop of binop * expr * expr
          | Var of id
          | Num of int

(**********************************************************************)

open Printf

let fprintf_bop out = function
  | Plus  -> fprintf out "+"
  | Minus -> fprintf out "-"
  | Times -> fprintf out "*"
  | Div   -> fprintf out "/"

let rec fprintf_type out = function
  | Int -> fprintf out "int"
  | Fun (t1, t2) -> fprintf out "(%a -> %a)" fprintf_type t1 fprintf_type t2

let rec fprintf_expr out = function
  | Num n -> fprintf out "%d" n
  | Var v -> fprintf out "%s" v
  | Binop (b, e1, e2) ->
    fprintf out "(%a %a %a)" fprintf_expr e1 fprintf_bop b fprintf_expr e2
  | Lam (i, ty, e) ->
    fprintf out "(\\%s : %a.%a)" i fprintf_type ty fprintf_expr e
  | App (e1, e2) ->
    fprintf out "%a %a" fprintf_expr e1 fprintf_expr e2

(**********************************************************************)

exception TypeMismatch of typ * typ
exception TypeError of string * typ
exception OpenExpr of id

(* Typechecking *)

(* assert_equal_type checks that the two type arguments are equivalent.
 * Only run for the side effect of raising the TypeMismatch exn if not. *)
let rec assert_equal_type = function
  | (Int, Int) -> ()
  | (Fun (t1, t2), Fun (t1', t2')) ->
    assert_equal_type (t1, t1'); assert_equal_type (t2, t2')
  | (t1, t2) -> raise (TypeMismatch (t1, t2))

(* tc_expr takes an environment and an expression to check, returning the
 * type of the expression if typechecking succeeds.
 * That is, tc_expr implements the judgment Γ ⊢ e : τ. *)
let rec tc_expr env = function
  (* --------------
   *  Γ ⊢ n : Int  *)
  | Num n -> Int
  (*     Γ(x) = τ
   *  --------------
   *    Γ ⊢ x : τ  
   * 
   * If the variable isn't in the environment, then we have an open expr. *)
  | Var v -> (try List.assoc v env with Not_found -> raise (OpenExpr v))
  (* Currently we just have Int * Int -> Int operations, so...
   *
   *  Γ ⊢ e1 : int    Γ ⊢ e2 : int
   *  -----------------------------
   *     Γ ⊢ e1 op e2 : int        *)
  | Binop (b, e1, e2) ->
    assert_equal_type ((tc_expr env e1), Int);
    assert_equal_type ((tc_expr env e2), Int);
    Int
  (*      Γ, x:τ1 ⊢ e : τ2
   *  -------------------------
   *    Γ ⊢ λx:t1.e : t1 → t2  *)
  | Lam (i, ty, e) ->
    Fun (ty, tc_expr ((i, ty) :: env) e)
  (*   Γ ⊢ e1 : τ1 → τ2    Γ ⊢ e2 : τ1
   *  ---------------------------------
   *         Γ ⊢ e1 e2 : t2            *)
  | App (e1, e2) ->
    (match tc_expr env e1 with
      | Fun (t1, t2) -> assert_equal_type ((tc_expr env e2), t1); t2
      | t -> raise (TypeError ("Expected arrow type, got type", t)))

let typecheck e = tc_expr [] e

(**********************************************************************)

(* Helpers for Evaluation *)

(* With typechecking, we should never get the following exception. *)
exception EvalError of string * expr
(* Since we have division, we can get the built-in Division_by_zero exn,
 * and our type system does not protect against that. *)

(* subst x v e = e[x ↦ v]
 * This subst does not worry about capture in the value being substituted
 * for the variable since I assume that we're working on closed expressions
 * and we're call-by-value. Our typechecker will fail on open expressions.
 *)
let rec subst id v = function
  (* n[x ↦ v] = n *)
  | Num n -> Num n
  (* x[x ↦ v] = v
     x1[x2 ↦ v] = x1 where x1 ≠ x2 *)
  | Var i -> if i = id then v else Var i
  (* (e1 op e2)[x ↦ v] = e1[x ↦ v] op e2[x ↦ v] *)
  | Binop (b, e1, e2) -> Binop (b, subst id v e1, subst id v e2)
  (* (λx:τ.e)[x ↦ v] = λx:τ.e
     (λx1:τ.e)[x2 ↦ v] = λx1:τ.e[x2 ↦ v] where x1 ≠ x2 *)
  | Lam (i, ty, e) ->
    if id = i then Lam (i, ty, e) else Lam (i, ty, subst id v e)
  (* (e1 e2)[x ↦ v] = e1[x ↦ v] e2[x ↦ v] *)
  | App (e1, e2) -> App (subst id v e1, subst id v e2)

(* These assert functions just keep us from getting non-exhaustive match
 * warnings (and also provide a more useful exception than No_match). *)
let assert_num = function
  | Num n -> n
  | e -> raise (EvalError ("Expected number, got", e))

let assert_lam = function
  | Lam (i, ty, e) -> (i, ty, e)
  | e -> raise (EvalError ("Expected lambda, got", e))

(**********************************************************************)

(* Big-Step or Natural Semantics *)

(* eval e = v when e ⇓ v *)
let rec eval = function
  (* n ⇓ n *)
  | Num n -> Num n
  (* λx:τ.e ⇓ λx:τ.e *)
  | Lam (id, ty, body) -> Lam (id, ty, body)
  (* No evaluation rule for open variables. *)
  | Var v -> raise (OpenExpr v)
  (*  e1 ⇓ n1      e2 ⇓ n2
   * ---------------------  where n3 = n1 + n2
   *    e1 + e2 ⇓ n3
   *
   * Similarly for -, *, / *)
  | Binop (b, e1, e2) ->
    let n1 = assert_num (eval e1) in
    let n2 = assert_num (eval e2) in
    (match b with
      | Plus  -> Num (n1 + n2)
      | Minus -> Num (n1 - n2)
      | Times -> Num (n1 * n2)
      | Div   -> Num (n1 / n2))
  (*  e1 ⇓ λx:τ.e     e2 ⇓ v
     ------------------------
         e1 e2 ⇓ e[x ↦ v]    *)
  | App (e1, e2) ->
    let (id, ty, body) = assert_lam (eval e1) in
    let arg = eval e2 in
    subst id arg body

(**********************************************************************)

(* Small Step or Structured Operational Semantics *)

(* Predicate for value expressions. *)
let value = function
  | Num n -> true
  | Lam (i, ty, e) -> true
  | _ -> false

(* step_one e = e' when e ↝ e' *)
let rec step_one = function
  | Binop (b, e1, e2) ->
    if value e1
    then
      if value e2
      (* n1 + n2 ↝ n3 where n3 = n1 + n2 (similarly for - * /) *)
      then let n1 = assert_num e1 in
           let n2 = assert_num e2 in
           (match b with
               Plus  -> Num (n1 + n2)
             | Minus -> Num (n1 - n2)
             | Times -> Num (n1 * n2)
             | Div   -> Num (n1 / n2))
      (*        e2 ↝ e2'
       * ----------------------
       *  v1 op e2 ↝ v1 op e2' *)
      else Binop (b, e1, step_one e2)
    (*        e1 ↝ e1'
     * ----------------------
     *  e1 op e2 ↝ e1' op e2 *)
    else Binop (b, step_one e1, e2)
  | App (e1, e2) ->
    if value e1
    then
      if value e2
      (* (λx:τ.e) v ↝ e[x ↦ v] *)
      then let (i, ty, body) = assert_lam e1
           in subst i e2 body
      (*     e2 ↝ e2'
       * -----------------
       *  v1 e2 ↝ v1 e2' *)
      else App (e1, step_one e2)
    (*      e1 ↝ e1'
     * -----------------
     *  e1 e2 ↝ e1' e2  *)
    else App (step_one e1, e2)
  | e -> raise (EvalError ("Should not try to step", e))

(* Reflexive, transitive closure of ↝, so step_many e = v when e ↝* v *)
let rec step_many e =
  if value e
  then e
  else step_many (step_one e)

(**********************************************************************)

(* Reduction Semantics *)

(* E = [] | E e | v E | E op e | v op E
 *
 * Here, we'll use expr for v, and just keep that invariant manually. *)
type ctx = Hole
           | AppLeft of ctx * expr
           | AppRight of expr * ctx
           | OpLeft of binop * ctx * expr
           | OpRight of binop * expr * ctx

(* Used to assert the argument is a value in beta reduction *)
let assert_value e =
  if value e then () else raise (EvalError ("Expected value, got", e))

(* Performs the unique decomposition of e into E[e'] and returns (E, e'). *)
let rec split = function
  | Num n -> (Hole, Num n)
  | Lam (i, ty, e) -> (Hole, Lam (i, ty, e))
  | Var x -> raise (OpenExpr x)
  | Binop (b, e1, e2) ->
    if value e1
    then 
      if value e2
      then (Hole, Binop (b, e1, e2))
      else let (c, e) = split e2
           in (OpRight (b, e1, c), e)
    else let (c, e) = split e1
         in (OpLeft (b, c, e2), e)
  | App (e1, e2) ->
    if value e1
    then
      if value e2
      then (Hole, App (e1, e2))
      else let (c, e) = split e2
           in (AppRight (e1, c), e)
    else let (c, e) = split e1
         in (AppLeft (c, e2), e)

(* Takes an expression and a context and recomposes them into an expression. *)
let rec recompose e = function
  | Hole -> e
  | OpLeft   (b, c, e2) -> Binop (b, recompose e c, e2)
  | OpRight  (b, e1, c) -> Binop (b, e1, recompose e c)
  | AppLeft  (c, e2)    -> App (recompose e c, e2)
  | AppRight (e1, c)    -> App (e1, recompose e c)

(* Performs the reduction rules e ↪ e' of our language. *)
let rec red_step = function
  (* n1 + n2 ↪ n3, where n3 = n1 + n2 (similarly for -, *, /) *)
  | Binop (b, e1, e2) ->
    let n1 = assert_num e1 in
    let n2 = assert_num e2 in
    (match b with
      | Plus  -> Num (n1 + n2)
      | Minus -> Num (n1 - n2)
      | Times -> Num (n1 * n2)
      | Div   -> Num (n1 / n2))
  (* (λx:τ.e) v ↪ e[x ↦ v] *)
  | App (e1, e2) ->
    let (id, ty, body) = assert_lam e1 in
    assert_value e2;
    subst id e2 body
  | e ->
    raise (EvalError ("unexpected expression to step:", e))

(* Performs the reflexive, transitive closure of ⇒, where ⇒ is the compatible
 * closure of ↪ (that is, E[e] ⇒ E[e'] if e ↪ e').
 * I.e., step_closure e = v if e ⇒* v. *)
let rec reduction_relation e =
  if value e
  then e
  else let (c, e') = split e in reduction_relation (recompose (red_step e') c)

(**********************************************************************)

(* Testing framework, prints out "e : t ⇓ v, ↝* v, ⇒* v" for success,
 * otherwise prints an error after printing out the original expression
 * (and type if the error is only in evaluation, which should only happen
 * for division by zero). *)

let test_expr e =
  fprintf_expr stdout e;
  (try (let ty = typecheck e in
        printf " : %a" fprintf_type ty;
        let v = eval e in
        printf " ⇓ %a" fprintf_expr v;
        let v = step_many e in
        printf ", ↝* %a" fprintf_expr v;
        let v = reduction_relation e in
        printf ", ⇒* %a\n" fprintf_expr v)
   with TypeMismatch (t1, t2) ->
     printf "\nERROR: Type %a does not match type %a\n"
       fprintf_type t1 fprintf_type t2
     | TypeError (s, ty) ->
       printf "\nERROR: %s %a\n" s fprintf_type ty
     | OpenExpr i ->
       printf "\nERROR: Variable %s unbound\n" i
     | Division_by_zero ->
       printf "\nERROR: Division by zero\n"
     | EvalError (s, exp) ->
       printf "\nERROR: %s %a\n" s fprintf_expr exp)

(* Passing testcases *)

let test1 = Num 5

let test2 = Lam ("x", Int, Var "x")

let test3 = App (Lam ("x", Int, Var "x"), Num 3)

let test4 = App (App (Lam ("x", Int, Lam ("y", Int, Var "x")), Num 4), Num 5)

let test5 = Binop (Plus, Num 3, Num 4);;

test_expr test1;;
test_expr test2;;
test_expr test3;;
test_expr test4;;
test_expr test5;;

(* Failing testcases *)

let fail1 = Var "x"
let fail2 = Lam ("x", Int, App (Var "x", Num 3))
let fail3 = App (Lam ("x", Int, Var "x"), Lam ("x", Int, Var "x"));;
let fail4 = Binop (Plus, Lam ("x", Int, Var "x"), Num 5);;
let fail5 = Binop (Div, Num 3, Num 0);;

test_expr fail1;;
test_expr fail2;;
test_expr fail3;;
test_expr fail4;;
test_expr fail5;;

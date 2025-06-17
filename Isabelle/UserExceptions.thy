theory UserExceptions
  imports Main
begin

(* User-related exceptions *)
datatype user_exception = 
  UserNotFoundException string nat |
  UserAlreadyExistsException string nat

(* Exception constructors *)
definition make_user_not_found :: "string ⇒ user_exception" where
  "make_user_not_found message = UserNotFoundException message 404"

definition make_user_already_exists :: "string ⇒ user_exception" where
  "make_user_already_exists message = UserAlreadyExistsException message 409"

(* Exception message extractors *)
fun exception_message :: "user_exception ⇒ string" where
  "exception_message (UserNotFoundException msg _) = msg" |
  "exception_message (UserAlreadyExistsException msg _) = msg"

fun exception_code :: "user_exception ⇒ nat" where
  "exception_code (UserNotFoundException _ code) = code" |
  "exception_code (UserAlreadyExistsException _ code) = code"

(* Exception type predicates *)
fun is_not_found_exception :: "user_exception ⇒ bool" where
  "is_not_found_exception (UserNotFoundException _ _) = True" |
  "is_not_found_exception _ = False"

fun is_already_exists_exception :: "user_exception ⇒ bool" where
  "is_already_exists_exception (UserAlreadyExistsException _ _) = True" |
  "is_already_exists_exception _ = False"

(* Result type for operations that can fail *)
datatype 'a user_result = Success 'a | Failure user_exception

(* Result operations *)
fun is_success :: "'a user_result ⇒ bool" where
  "is_success (Success _) = True" |
  "is_success (Failure _) = False"

fun get_success :: "'a user_result ⇒ 'a option" where
  "get_success (Success x) = Some x" |
  "get_success (Failure _) = None"

fun get_failure :: "'a user_result ⇒ user_exception option" where
  "get_failure (Success _) = None" |
  "get_failure (Failure e) = Some e"

(* Exception properties *)
lemma user_not_found_code:
  "exception_code (make_user_not_found msg) = 404"
  unfolding make_user_not_found_def by simp

lemma user_already_exists_code:
  "exception_code (make_user_already_exists msg) = 409"
  unfolding make_user_already_exists_def by simp

lemma exception_type_exclusivity:
  "is_not_found_exception e ⟹ ¬is_already_exists_exception e"
  by (cases e) auto

lemma success_failure_exclusivity:
  "is_success r ⟹ get_failure r = None"
  by (cases r) auto

end 
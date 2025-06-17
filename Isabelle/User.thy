theory User
  imports Main
begin

(* User entity representation *)
record user = 
  user_id :: nat
  user_email :: string  
  user_name :: string
  user_created_at :: string
  user_is_active :: bool

(* Email validation function *)
fun is_valid_email :: "string ⇒ bool" where
  "is_valid_email email = (email ≠ [] ∧ ''@'' ∈ set email)"

(* User constructor with validation *)
fun make_user :: "nat ⇒ string ⇒ string ⇒ bool ⇒ user option" where
  "make_user id email name active = 
    (if is_valid_email email ∧ name ≠ [] then 
      Some ⌊user_id = id, user_email = email, user_name = name, 
            user_created_at = ''2024-01-01'', user_is_active = active⌋
     else None)"

(* User operations *)
fun set_user_email :: "user ⇒ string ⇒ user option" where
  "set_user_email u email = 
    (if is_valid_email email then 
      Some (u⌊user_email := email⌋) 
     else None)"

fun set_user_name :: "user ⇒ string ⇒ user option" where
  "set_user_name u name = 
    (if name ≠ [] then 
      Some (u⌊user_name := name⌋) 
     else None)"

fun activate_user :: "user ⇒ user" where
  "activate_user u = u⌊user_is_active := True⌋"

fun deactivate_user :: "user ⇒ user" where
  "deactivate_user u = u⌊user_is_active := False⌋"

(* User to array conversion *)
fun user_to_list :: "user ⇒ (string × string) list" where
  "user_to_list u = [
    (''id'', show (user_id u)),
    (''email'', user_email u),
    (''name'', user_name u), 
    (''created_at'', user_created_at u),
    (''is_active'', if user_is_active u then ''true'' else ''false'')
  ]"

(* Basic properties *)
lemma user_email_validation:
  "make_user id email name active = Some u ⟹ is_valid_email email"
  by (cases "is_valid_email email ∧ name ≠ []") auto

lemma user_name_not_empty:
  "make_user id email name active = Some u ⟹ name ≠ []"
  by (cases "is_valid_email email ∧ name ≠ []") auto

lemma activate_preserves_data:
  "user_id (activate_user u) = user_id u ∧
   user_email (activate_user u) = user_email u ∧
   user_name (activate_user u) = user_name u"
  by simp

end 
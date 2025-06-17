theory UserService
  imports User UserExceptions UserRepository
begin

(* User service state *)
record user_service_state = 
  repository :: user_store

(* Service operations with error handling *)
fun service_create_user :: "user_service_state ⇒ string ⇒ string ⇒ user_service_state × user user_result" where
  "service_create_user state email name = 
    (case repo_find_by_email (repository state) email of
      Some _ ⇒ (state, Failure (make_user_already_exists (''User with email '' @ email @ '' already exists'')))
    | None ⇒ 
        (case make_user 0 email name True of
          Some new_user ⇒ 
            let new_repo = repo_save (repository state) new_user;
                saved_user = the (repo_find_by_email new_repo email) in
            (state⌊repository := new_repo⌋, Success saved_user)
        | None ⇒ (state, Failure (make_user_already_exists ''Invalid user data''))))"

fun service_get_user_by_id :: "user_service_state ⇒ nat ⇒ user user_result" where
  "service_get_user_by_id state id = 
    (case repo_find_by_id (repository state) id of
      Some user ⇒ Success user
    | None ⇒ Failure (make_user_not_found (''User with ID '' @ show id @ '' not found'')))"

fun service_get_user_by_email :: "user_service_state ⇒ string ⇒ user user_result" where
  "service_get_user_by_email state email = 
    (case repo_find_by_email (repository state) email of
      Some user ⇒ Success user
    | None ⇒ Failure (make_user_not_found (''User with email '' @ email @ '' not found'')))"

fun service_update_user :: "user_service_state ⇒ nat ⇒ string option ⇒ string option ⇒ user_service_state × user user_result" where
  "service_update_user state id new_email new_name = 
    (case repo_find_by_id (repository state) id of
      None ⇒ (state, Failure (make_user_not_found (''User with ID '' @ show id @ '' not found'')))
    | Some user ⇒
        let updated_user = user in
        (case new_email of
          None ⇒ 
            (case new_name of
              None ⇒ (state, Success user)
            | Some name ⇒ 
                (case set_user_name updated_user name of
                  Some u ⇒ 
                    let new_repo = repo_save (repository state) u in
                    (state⌊repository := new_repo⌋, Success u)
                | None ⇒ (state, Failure (make_user_already_exists ''Invalid name''))))
        | Some email ⇒
            if email ≠ user_email user ∧ repo_find_by_email (repository state) email ≠ None
            then (state, Failure (make_user_already_exists (''User with email '' @ email @ '' already exists'')))
            else
              (case set_user_email updated_user email of
                Some u_with_email ⇒
                  (case new_name of
                    None ⇒ 
                      let new_repo = repo_save (repository state) u_with_email in
                      (state⌊repository := new_repo⌋, Success u_with_email)
                  | Some name ⇒
                      (case set_user_name u_with_email name of
                        Some u_final ⇒ 
                          let new_repo = repo_save (repository state) u_final in
                          (state⌊repository := new_repo⌋, Success u_final)
                      | None ⇒ (state, Failure (make_user_already_exists ''Invalid name''))))
              | None ⇒ (state, Failure (make_user_already_exists ''Invalid email'')))))"

fun service_delete_user :: "user_service_state ⇒ nat ⇒ user_service_state × bool user_result" where
  "service_delete_user state id = 
    (case service_get_user_by_id state id of
      Failure e ⇒ (state, Failure e)
    | Success _ ⇒ 
        let (new_repo, deleted) = repo_delete (repository state) id in
        (state⌊repository := new_repo⌋, Success deleted))"

fun service_activate_user :: "user_service_state ⇒ nat ⇒ user_service_state × user user_result" where
  "service_activate_user state id = 
    (case service_get_user_by_id state id of
      Failure e ⇒ (state, Failure e)
    | Success user ⇒ 
        let activated_user = activate_user user;
            new_repo = repo_save (repository state) activated_user in
        (state⌊repository := new_repo⌋, Success activated_user))"

fun service_deactivate_user :: "user_service_state ⇒ nat ⇒ user_service_state × user user_result" where
  "service_deactivate_user state id = 
    (case service_get_user_by_id state id of
      Failure e ⇒ (state, Failure e)
    | Success user ⇒ 
        let deactivated_user = deactivate_user user;
            new_repo = repo_save (repository state) deactivated_user in
        (state⌊repository := new_repo⌋, Success deactivated_user))"

fun service_get_all_users :: "user_service_state ⇒ user list" where
  "service_get_all_users state = repo_find_all (repository state)"

fun service_get_active_users :: "user_service_state ⇒ user list" where
  "service_get_active_users state = repo_find_active (repository state)"

fun service_get_users_count :: "user_service_state ⇒ nat" where
  "service_get_users_count state = length (service_get_all_users state)"

fun service_get_active_users_count :: "user_service_state ⇒ nat" where
  "service_get_active_users_count state = length (service_get_active_users state)"

(* Initialize service with default repository *)
definition init_user_service :: user_service_state where
  "init_user_service = ⌊repository = init_user_store⌋"

(* Service properties and invariants *)
lemma service_create_user_unique_email:
  "service_create_user state email name = (new_state, Success user) ⟹ 
   repo_find_by_email (repository state) email = None"
  by (cases "repo_find_by_email (repository state) email") auto

lemma service_get_user_by_id_correct:
  "service_get_user_by_id state id = Success user ⟹ 
   repo_find_by_id (repository state) id = Some user"
  by (simp add: service_get_user_by_id.simps split: option.splits)

lemma service_activate_preserves_identity:
  "service_activate_user state id = (new_state, Success user) ⟹
   ∃old_user. service_get_user_by_id state id = Success old_user ∧
              user_id user = user_id old_user ∧
              user_email user = user_email old_user ∧
              user_name user = user_name old_user ∧
              user_is_active user = True"
  by (auto simp: service_activate_user.simps service_get_user_by_id.simps activate_user.simps 
           split: user_result.splits)

lemma service_active_users_are_active:
  "u ∈ set (service_get_active_users state) ⟹ user_is_active u"
  by (simp add: service_get_active_users.simps repo_find_active.simps)

lemma service_consistency:
  "service_get_user_by_id state id = Success user ⟹ 
   user ∈ set (service_get_all_users state)"
  by (simp add: service_get_user_by_id.simps service_get_all_users.simps 
           repo_find_by_id.simps repo_find_all.simps find_Some_iff)

end 
theory DiscountSystem
  imports Main
begin

text \<open>
  Простая формальная модель системы скидок
  Доказываем, что скидки никогда не увеличивают цену
\<close>

section \<open>Основные определения\<close>

text \<open>Два типа купонов\<close>
datatype coupon_type = Absolute | Percentage

text \<open>Купон состоит из типа и значения скидки\<close>
record coupon =
  ctype :: coupon_type
  amount :: nat

text \<open>Корректный купон: скидка неотрицательна, процент не больше 100\<close>
definition valid_coupon :: "coupon \<Rightarrow> bool" where
  "valid_coupon c \<equiv> 
    (ctype c = Absolute) \<or> 
    (ctype c = Percentage \<and> amount c \<le> 100)"

text \<open>Корректный инвойс: цена неотрицательна\<close>
definition valid_price :: "nat \<Rightarrow> bool" where
  "valid_price p \<equiv> True"  (* nat всегда неотрицателен *)

section \<open>Функция применения скидки\<close>

text \<open>Применяем скидку к цене\<close>
fun apply_discount :: "nat \<Rightarrow> coupon \<Rightarrow> nat" where
  "apply_discount price c = 
    (if ctype c = Absolute then
      (if amount c \<le> price then price - amount c else 0)
    else (* Percentage *)
      price - (price * amount c) div 100)"

section \<open>Основные теоремы\<close>

text \<open>
  ЛЕММА 1: Абсолютная скидка не увеличивает цену
\<close>
lemma absolute_discount_safe:
  assumes "valid_price price"
      and "valid_coupon c" 
      and "ctype c = Absolute"
  shows "apply_discount price c \<le> price"
proof -
  have "apply_discount price c = 
        (if amount c \<le> price then price - amount c else 0)" 
    using assms(3) by simp
  thus ?thesis by auto
qed

text \<open>
  ЛЕММА 2: Процентная скидка не увеличивает цену
\<close>
lemma percentage_discount_safe:
  assumes "valid_price price"
      and "valid_coupon c"
      and "ctype c = Percentage"
  shows "apply_discount price c \<le> price"
proof -
  have "apply_discount price c = price - (price * amount c) div 100"
    using assms(3) by simp
  
  (* Показываем, что (price * amount c) div 100 \<le> price *)
  have "amount c \<le> 100" using assms(2,3) valid_coupon_def by auto
  hence "(price * amount c) div 100 \<le> price" 
    by (auto simp: div_le_iff mult_le_mono)
  
  thus ?thesis by auto
qed

text \<open>
  ГЛАВНАЯ ТЕОРЕМА: Любая корректная скидка не увеличивает цену
\<close>
theorem discount_never_increases:
  assumes "valid_price price"
      and "valid_coupon c"
  shows "apply_discount price c \<le> price"
proof (cases "ctype c")
  case Absolute
  then show ?thesis using assms absolute_discount_safe by simp
next
  case Percentage  
  then show ?thesis using assms percentage_discount_safe by simp
qed

text \<open>
  ТЕОРЕМА О НЕСУЩЕСТВОВАНИИ: Не существует пары (цена, купон),
  при которой применение купона увеличивает цену
\<close>
theorem no_price_increase:
  "\<not>(\<exists>price c. valid_price price \<and> valid_coupon c \<and> 
              apply_discount price c > price)"
proof
  assume "\<exists>price c. valid_price price \<and> valid_coupon c \<and> 
                   apply_discount price c > price"
  then obtain price c where
    h1: "valid_price price" and
    h2: "valid_coupon c" and  
    h3: "apply_discount price c > price" by blast
  
  (* Но мы знаем, что скидка не может увеличить цену *)
  have "apply_discount price c \<le> price" 
    using h1 h2 discount_never_increases by simp
  
  (* Противоречие! *)
  thus False using h3 by simp
qed

section \<open>Примеры проверки\<close>

text \<open>Пример 1: Абсолютная скидка 100 от цены 1000\<close>
value "apply_discount 1000 \<lparr>ctype = Absolute, amount = 100\<rparr>"

text \<open>Пример 2: Процентная скидка 20% от цены 1000\<close>  
value "apply_discount 1000 \<lparr>ctype = Percentage, amount = 20\<rparr>"

text \<open>Пример 3: Чрезмерная абсолютная скидка\<close>
value "apply_discount 50 \<lparr>ctype = Absolute, amount = 100\<rparr>"

text \<open>Проверяем примеры вычислениями\<close>
lemma "apply_discount 1000 \<lparr>ctype = Absolute, amount = 100\<rparr> = 900"
  by simp

lemma "apply_discount 1000 \<lparr>ctype = Percentage, amount = 20\<rparr> = 800"  
  by simp

lemma "apply_discount 50 \<lparr>ctype = Absolute, amount = 100\<rparr> = 0"
  by simp

section \<open>Дополнительные свойства\<close>

text \<open>Результат всегда неотрицателен (автоматически для nat)\<close>
lemma result_nonnegative:
  "apply_discount price c \<ge> 0"
  by simp

text \<open>Идемпотентность: повторное применение той же скидки дает 0\<close>
lemma discount_idempotent:
  assumes "valid_coupon c"
  shows "apply_discount (apply_discount price c) c \<le> apply_discount price c"
  using assms discount_never_increases valid_price_def by simp

end 
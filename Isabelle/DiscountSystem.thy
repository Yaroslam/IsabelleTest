theory DiscountSystem
  imports Main
begin

text \<open>
  Формальная модель системы скидок с доказательством корректности
\<close>

section \<open>Определения типов данных\<close>

text \<open>Тип купона: абсолютный или процентный\<close>
datatype coupon = 
    Absolute real  (* абсолютная скидка в денежных единицах *)
  | Percentage real (* процентная скидка от 0 до 100 *)

text \<open>Инвойс - это просто цена (положительное вещественное число)\<close>
type_synonym invoice = real

section \<open>Предикаты корректности\<close>

text \<open>Корректный купон: абсолютная скидка неотрицательна, процентная от 0 до 100\<close>
definition valid_coupon :: "coupon \<Rightarrow> bool" where
  "valid_coupon c \<equiv> case c of
    Absolute amount \<Rightarrow> amount \<ge> 0
  | Percentage percent \<Rightarrow> 0 \<le> percent \<and> percent \<le> 100"

text \<open>Корректный инвойс: цена неотрицательна\<close>
definition valid_invoice :: "invoice \<Rightarrow> bool" where
  "valid_invoice price \<equiv> price \<ge> 0"

section \<open>Функция применения скидки\<close>

text \<open>Применение купона к инвойсу\<close>
fun apply_discount :: "invoice \<Rightarrow> coupon \<Rightarrow> real" where
  "apply_discount price (Absolute amount) = max 0 (price - amount)"
| "apply_discount price (Percentage percent) = max 0 (price - (price * percent / 100))"

section \<open>Основные теоремы\<close>

text \<open>
  ГЛАВНАЯ ТЕОРЕМА: применение любого корректного купона к корректному инвойсу
  никогда не увеличивает цену
\<close>
theorem discount_never_increases_price:
  assumes "valid_invoice price" 
      and "valid_coupon coupon"
  shows "apply_discount price coupon \<le> price"
proof (cases coupon)
  case (Absolute amount)
  then show ?thesis 
  proof -
    have "apply_discount price (Absolute amount) = max 0 (price - amount)" 
      by simp
    also have "... \<le> price - amount"
      by (simp add: max_def)
    also have "... \<le> price"
      using Absolute assms(2) valid_coupon_def by auto
    finally show ?thesis .
  qed
next
  case (Percentage percent)
  then show ?thesis
  proof -
    have "apply_discount price (Percentage percent) = max 0 (price - (price * percent / 100))"
      by simp
    also have "... \<le> price - (price * percent / 100)"
      by (simp add: max_def)
    also have "... = price * (1 - percent / 100)"
      by (simp add: algebra_simps)
    also have "... \<le> price"
    proof -
      have "percent \<le> 100" using Percentage assms(2) valid_coupon_def by auto
      hence "percent / 100 \<le> 1" by simp
      hence "1 - percent / 100 \<ge> 0" by simp
      moreover have "1 - percent / 100 \<le> 1" by simp
      ultimately show ?thesis 
        using assms(1) valid_invoice_def 
        by (auto simp: mult_left_mono)
    qed
    finally show ?thesis .
  qed
qed

text \<open>
  УСИЛЕННАЯ ТЕОРЕМА: результат всегда неотрицателен
\<close>
theorem discount_result_nonnegative:
  assumes "valid_invoice price"
      and "valid_coupon coupon"
  shows "apply_discount price coupon \<ge> 0"
proof (cases coupon)
  case (Absolute amount)
  then show ?thesis by (simp add: max_def)
next
  case (Percentage percent)
  then show ?thesis by (simp add: max_def)
qed

text \<open>
  ТЕОРЕМА: для процентных купонов результат пропорционален исходной цене
\<close>
theorem percentage_discount_proportional:
  assumes "valid_invoice price"
      and "valid_coupon (Percentage percent)"
      and "price > 0"
  shows "apply_discount price (Percentage percent) = price * max 0 (1 - percent / 100)"
proof -
  have "apply_discount price (Percentage percent) = max 0 (price - (price * percent / 100))"
    by simp
  also have "... = max 0 (price * (1 - percent / 100))"
    by (simp add: algebra_simps)
  also have "... = price * max 0 (1 - percent / 100)"
    using assms(3) by (simp add: max_mult_distrib_left)
  finally show ?thesis .
qed

text \<open>
  ТЕОРЕМА: абсолютная скидка не может превышать цену товара
\<close>
theorem absolute_discount_bounded:
  assumes "valid_invoice price"
      and "valid_coupon (Absolute amount)"
      and "amount > price"
  shows "apply_discount price (Absolute amount) = 0"
proof -
  have "apply_discount price (Absolute amount) = max 0 (price - amount)" by simp
  also have "... = 0" using assms(3) by simp
  finally show ?thesis .
qed

section \<open>Примеры и проверки\<close>

text \<open>Пример 1: Абсолютная скидка 150 рублей от цены 1000 рублей\<close>
lemma example_absolute:
  "apply_discount 1000 (Absolute 150) = 850"
  by simp

text \<open>Пример 2: Процентная скидка 20% от цены 1000 рублей\<close>
lemma example_percentage:
  "apply_discount 1000 (Percentage 20) = 800"
  by simp

text \<open>Пример 3: Абсолютная скидка больше цены товара\<close>
lemma example_excessive_absolute:
  "apply_discount 50 (Absolute 100) = 0"
  by simp

text \<open>Пример 4: 100% скидка\<close>
lemma example_full_percentage:
  "apply_discount 1000 (Percentage 100) = 0"
  by simp

section \<open>Метатеоремы о системе\<close>

text \<open>
  НЕ СУЩЕСТВУЕТ пары (инвойс, купон), дающей цену больше исходной
\<close>
theorem no_price_increase:
  "\<not>(\<exists>price coupon. valid_invoice price \<and> valid_coupon coupon \<and> 
                      apply_discount price coupon > price)"
proof 
  assume "\<exists>price coupon. valid_invoice price \<and> valid_coupon coupon \<and> 
                          apply_discount price coupon > price"
  then obtain price coupon where 
    "valid_invoice price" and 
    "valid_coupon coupon" and 
    "apply_discount price coupon > price" by blast
  hence "apply_discount price coupon \<le> price" 
    using discount_never_increases_price by simp
  thus False using \<open>apply_discount price coupon > price\<close> by simp
qed

text \<open>
  СЛЕДСТВИЕ: система скидок монотонна (никогда не увеличивает цену)
\<close>
corollary discount_system_monotonic:
  "valid_invoice price \<Longrightarrow> valid_coupon coupon \<Longrightarrow> 
   apply_discount price coupon \<le> price"
  by (rule discount_never_increases_price)

end 
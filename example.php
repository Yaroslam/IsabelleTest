<?php

require_once 'vendor/autoload.php';

use App\Coupon\AbsoluteCoupon;
use App\Coupon\PercentageCoupon;
use App\Invoice\Invoice;
use App\Service\DiscountService;

// Создаем инвойс с ценой 1000 рублей
$invoice = new Invoice(1000.0);

// Создаем купоны
$absoluteCoupon = new AbsoluteCoupon(150.0); // скидка 150 рублей
$percentageCoupon = new PercentageCoupon(20.0); // скидка 20%

// Создаем сервис скидок
$discountService = new DiscountService();

echo "=== Пример работы системы скидок ===\n";
echo "Первоначальная цена инвойса: " . $invoice->getPrice() . " руб.\n\n";

// Применяем абсолютную скидку
$finalPriceAbsolute = $discountService->applyDiscount($invoice, $absoluteCoupon);
$discountAmountAbsolute = $discountService->calculateDiscountAmount($invoice, $absoluteCoupon);

echo "Абсолютная скидка " . $absoluteCoupon->getDiscount() . " руб.:\n";
echo "  Размер скидки: " . $discountAmountAbsolute . " руб.\n";
echo "  Итоговая цена: " . $finalPriceAbsolute . " руб.\n\n";

// Применяем процентную скидку
$finalPricePercentage = $discountService->applyDiscount($invoice, $percentageCoupon);
$discountAmountPercentage = $discountService->calculateDiscountAmount($invoice, $percentageCoupon);

echo "Процентная скидка " . $percentageCoupon->getDiscount() . "%:\n";
echo "  Размер скидки: " . $discountAmountPercentage . " руб.\n";
echo "  Итоговая цена: " . $finalPricePercentage . " руб.\n\n";

// Тестируем крайние случаи
echo "=== Тестирование крайних случаев ===\n";

// Абсолютная скидка больше цены товара
$smallInvoice = new Invoice(50.0);
$bigAbsoluteCoupon = new AbsoluteCoupon(100.0);
$finalPriceSmall = $discountService->applyDiscount($smallInvoice, $bigAbsoluteCoupon);

echo "Инвойс 50 руб. + абсолютная скидка 100 руб.:\n";
echo "  Итоговая цена: " . $finalPriceSmall . " руб. (не может быть отрицательной)\n\n";

// Процентная скидка 100%
$fullPercentageCoupon = new PercentageCoupon(100.0);
$finalPriceFree = $discountService->applyDiscount($invoice, $fullPercentageCoupon);

echo "Инвойс 1000 руб. + процентная скидка 100%:\n";
echo "  Итоговая цена: " . $finalPriceFree . " руб.\n"; 
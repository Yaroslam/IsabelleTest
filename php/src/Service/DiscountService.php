<?php

namespace App\Service;

use App\Coupon\CouponInterface;
use App\Invoice\Invoice;

class DiscountService
{
    public function applyDiscount(Invoice $invoice, CouponInterface $coupon): float
    {
        $originalPrice = $invoice->getPrice();

        $discountAmount = match ($coupon->getType()) {
            'absolute' => min($coupon->getDiscount(), $originalPrice),
            'percentage' => ($originalPrice * $coupon->getDiscount()) / 100,
            default => throw new \InvalidArgumentException('Unknown coupon type: ' . $coupon->getType()),
        };

        return max(0, $originalPrice - $discountAmount);
    }

    public function calculateDiscountAmount(Invoice $invoice, CouponInterface $coupon): float
    {
        $originalPrice = $invoice->getPrice();
        $finalPrice = $this->applyDiscount($invoice, $coupon);
        
        return $originalPrice - $finalPrice;
    }
} 
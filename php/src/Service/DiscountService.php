<?php

namespace App\Service;

use App\Coupon\CouponInterface;
use App\Invoice\Invoice;

class DiscountService
{
    public function applyDiscount(Invoice $invoice, CouponInterface $coupon): float
    {
        $originalPrice = $invoice->getPrice();
        $discountAmount = 0;

        switch ($coupon->getType()) {
            case 'absolute':
                $discountAmount = min($coupon->getDiscount(), $originalPrice);
                break;
            case 'percentage':
                $discountAmount = ($originalPrice * $coupon->getDiscount()) / 100;
                break;
            default:
                throw new \InvalidArgumentException('Unknown coupon type: ' . $coupon->getType());
        }

        $finalPrice = max(0, $originalPrice - $discountAmount);
        
        return $finalPrice;
    }

    public function calculateDiscountAmount(Invoice $invoice, CouponInterface $coupon): float
    {
        $originalPrice = $invoice->getPrice();
        $finalPrice = $this->applyDiscount($invoice, $coupon);
        
        return $originalPrice - $finalPrice;
    }
} 
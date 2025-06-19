<?php

namespace App\Coupon;

class PercentageCoupon implements CouponInterface
{
    private float $discount;

    public function __construct(float $discount)
    {
        if ($discount < 0 || $discount > 100) {
            throw new \InvalidArgumentException('Percentage discount must be between 0 and 100');
        }
        $this->discount = $discount;
    }

    public function getDiscount(): float
    {
        return $this->discount;
    }

    public function getType(): string
    {
        return 'percentage';
    }
} 
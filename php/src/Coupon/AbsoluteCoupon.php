<?php

namespace App\Coupon;

class AbsoluteCoupon implements CouponInterface
{
    private float $discount;

    public function __construct(float $discount)
    {
        $this->discount = $discount;
    }

    public function getDiscount(): float
    {
        return $this->discount;
    }

    public function getType(): string
    {
        return 'absolute';
    }
} 
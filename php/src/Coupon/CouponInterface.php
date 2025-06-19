<?php

namespace App\Coupon;

interface CouponInterface
{
    public function getDiscount(): float;
    public function getType(): string;
} 
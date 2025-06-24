<?php

namespace App\Tests\Service;

use App\Coupon\AbsoluteCoupon;
use App\Coupon\PercentageCoupon;
use App\Invoice\Invoice;
use App\Service\DiscountService;
use PHPUnit\Framework\TestCase;

class DiscountServiceTest extends TestCase
{
    private DiscountService $discountService;

    protected function setUp(): void
    {
        $this->discountService = new DiscountService();
    }

    public function testApplyAbsoluteDiscountNormal(): void
    {
        $invoice = new Invoice(1000.0);
        $coupon = new AbsoluteCoupon(100.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(900.0, $result);
    }

    public function testApplyAbsoluteDiscountExceedsPrice(): void
    {
        $invoice = new Invoice(50.0);
        $coupon = new AbsoluteCoupon(100.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(0.0, $result);
    }

    public function testApplyAbsoluteDiscountEqualsPrice(): void
    {
        $invoice = new Invoice(100.0);
        $coupon = new AbsoluteCoupon(100.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(0.0, $result);
    }

    public function testApplyPercentageDiscountNormal(): void
    {
        $invoice = new Invoice(1000.0);
        $coupon = new PercentageCoupon(20.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(800.0, $result);
    }

    public function testApplyPercentageDiscountZeroPercent(): void
    {
        $invoice = new Invoice(1000.0);
        $coupon = new PercentageCoupon(0.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(1000.0, $result);
    }

    public function testApplyPercentageDiscount100Percent(): void
    {
        $invoice = new Invoice(1000.0);
        $coupon = new PercentageCoupon(100.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(0.0, $result);
    }

    public function testCalculateDiscountAmountAbsolute(): void
    {
        $invoice = new Invoice(1000.0);
        $coupon = new AbsoluteCoupon(100.0);

        $result = $this->discountService->calculateDiscountAmount($invoice, $coupon);

        $this->assertEquals(100.0, $result);
    }

    public function testCalculateDiscountAmountAbsoluteExceedsPrice(): void
    {
        $invoice = new Invoice(50.0);
        $coupon = new AbsoluteCoupon(100.0);

        $result = $this->discountService->calculateDiscountAmount($invoice, $coupon);

        $this->assertEquals(50.0, $result);
    }

    public function testCalculateDiscountAmountPercentage(): void
    {
        $invoice = new Invoice(1000.0);
        $coupon = new PercentageCoupon(20.0);

        $result = $this->discountService->calculateDiscountAmount($invoice, $coupon);

        $this->assertEquals(200.0, $result);
    }

    public function testApplyDiscountWithZeroPrice(): void
    {
        $invoice = new Invoice(0.0);
        $coupon = new AbsoluteCoupon(100.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertEquals(0.0, $result);
    }

    public function testResultNeverGoesNegative(): void
    {
        $invoice = new Invoice(100.0);
        $coupon = new AbsoluteCoupon(200.0);

        $result = $this->discountService->applyDiscount($invoice, $coupon);

        $this->assertGreaterThanOrEqual(0.0, $result);
        $this->assertEquals(0.0, $result);
    }
} 
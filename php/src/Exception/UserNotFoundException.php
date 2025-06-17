<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Exception;

use Exception;

class UserNotFoundException extends Exception
{
    public function __construct(string $message = 'User not found', int $code = 404, ?Exception $previous = null)
    {
        parent::__construct($message, $code, $previous);
    }
} 
<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Exception;

use Exception;

class UserAlreadyExistsException extends Exception
{
    public function __construct(string $message = 'User already exists', int $code = 409, ?Exception $previous = null)
    {
        parent::__construct($message, $code, $previous);
    }
} 
<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Repository;

use Yaroslam\Phpisabelle\Entity\User;

interface UserRepositoryInterface
{
    public function findById(int $id): ?User;
    
    public function findByEmail(string $email): ?User;
    
    public function findAll(): array;
    
    public function save(User $user): void;
    
    public function delete(int $id): bool;
    
    public function findActiveUsers(): array;
} 
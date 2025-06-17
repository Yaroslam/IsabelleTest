<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle;

use Yaroslam\Phpisabelle\Repository\InMemoryUserRepository;
use Yaroslam\Phpisabelle\Service\UserService;
use Yaroslam\Phpisabelle\Exception\UserNotFoundException;
use Yaroslam\Phpisabelle\Exception\UserAlreadyExistsException;

class Application
{
    private UserService $userService;

    public function __construct()
    {
        $userRepository = new InMemoryUserRepository();
        $this->userService = new UserService($userRepository);
    }

    public function run(): void
    {
        echo "=== User Management Application ===\n\n";

        try {
            // Показываем всех пользователей
            $this->displayAllUsers();

            // Создаем нового пользователя
            echo "\n--- Creating new user ---\n";
            $newUser = $this->userService->createUser('newuser@example.com', 'New User');
            echo "Created user: {$newUser->getName()} ({$newUser->getEmail()})\n";

            // Показываем всех пользователей после создания
            $this->displayAllUsers();

            // Обновляем пользователя
            echo "\n--- Updating user ---\n";
            $updatedUser = $this->userService->updateUser($newUser->getId(), null, 'Updated User Name');
            echo "Updated user: {$updatedUser->getName()}\n";

            // Деактивируем пользователя
            echo "\n--- Deactivating user ---\n";
            $deactivatedUser = $this->userService->deactivateUser($newUser->getId());
            echo "Deactivated user: {$deactivatedUser->getName()}\n";

            // Показываем только активных пользователей
            $this->displayActiveUsers();

            // Пытаемся найти несуществующего пользователя
            echo "\n--- Trying to find non-existent user ---\n";
            $this->userService->getUserById(999);

        } catch (UserNotFoundException $e) {
            echo "Error: {$e->getMessage()}\n";
        } catch (UserAlreadyExistsException $e) {
            echo "Error: {$e->getMessage()}\n";
        } catch (\Exception $e) {
            echo "Unexpected error: {$e->getMessage()}\n";
        }

        echo "\n=== Application finished ===\n";
    }

    private function displayAllUsers(): void
    {
        echo "\n--- All Users ---\n";
        $users = $this->userService->getAllUsers();
        
        if (empty($users)) {
            echo "No users found.\n";
            return;
        }

        foreach ($users as $user) {
            $status = $user->isActive() ? 'Active' : 'Inactive';
            echo "ID: {$user->getId()}, Name: {$user->getName()}, Email: {$user->getEmail()}, Status: {$status}\n";
        }
        
        echo "Total users: {$this->userService->getUsersCount()}\n";
    }

    private function displayActiveUsers(): void
    {
        echo "\n--- Active Users ---\n";
        $activeUsers = $this->userService->getActiveUsers();
        
        if (empty($activeUsers)) {
            echo "No active users found.\n";
            return;
        }

        foreach ($activeUsers as $user) {
            echo "ID: {$user->getId()}, Name: {$user->getName()}, Email: {$user->getEmail()}\n";
        }
        
        echo "Active users: {$this->userService->getActiveUsersCount()}\n";
    }
} 
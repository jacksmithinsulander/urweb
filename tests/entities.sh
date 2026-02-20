# Verify HTML entities are rendered (either as &entity; or literal UTF-8)
check Entities/main "Hello world!"
check Entities/main "&amp;"
check Entities/main "&copy;"
check Entities/main "&spades;"
check Entities/main "&dagger;"

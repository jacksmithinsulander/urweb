# Verify HTML entities are rendered as literal UTF-8
check Entities/main "Hello world!"
check Entities/main "&amp;"
check Entities/main "©"
check Entities/main "♠"
check Entities/main "†"

# WI-777 parser parity corpus

Both `rustland` and `scaland` consume these exact files. Directory names are the
expected parse verdict: every `accept/*.anthill` file must parse successfully and
every `reject/*.anthill` file must produce a parse/conversion diagnostic.

This corpus is intentionally parse-only. Its purpose is to pin the shared kernel
surface independently of either implementation's loader or typer.

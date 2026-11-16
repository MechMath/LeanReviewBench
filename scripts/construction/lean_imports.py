"""Read all modules on Lean import lines, excluding nested comments and strings."""
import re


class Imports:
    def findall(self, text):
        clean = []
        i, depth, string = 0, 0, False
        while i < len(text):
            if depth:
                if text.startswith('/-', i):
                    depth += 1
                    clean.extend('  ')
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    clean.extend('  ')
                    i += 2
                else:
                    clean.append('\n' if text[i] == '\n' else ' ')
                    i += 1
            elif string:
                if text[i] == '\\' and i + 1 < len(text):
                    clean.extend('  ')
                    i += 2
                else:
                    string = text[i] != '"'
                    clean.append('\n' if text[i] == '\n' else ' ')
                    i += 1
            elif text.startswith('/-', i):
                depth = 1
                clean.extend('  ')
                i += 2
            elif text.startswith('--', i):
                end = text.find('\n', i)
                end = len(text) if end < 0 else end
                clean.extend(' ' * (end - i))
                i = end
            elif text[i] == '"':
                string = True
                clean.append(' ')
                i += 1
            else:
                clean.append(text[i])
                i += 1
        modules = []
        # Lean permits a long import path on the line following `public import`.
        # Cross newlines before the first module, but stop at the next header.
        pattern = r'(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\s+(?:all\s+)?([^\s]+(?:[ \t]+[^\s]+)*)'
        for match in re.finditer(pattern, ''.join(clean)):
            modules.extend(module for module in match[1].split() if module != 'all')
        return modules


IMPORT = Imports()

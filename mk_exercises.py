#!/usr/bin/env python3

import re
from pathlib import Path

sorry_regex = re.compile(r'(.*)-- sorry.*')
root = Path(__file__).parent/'Tutorials'

if __name__ == '__main__':
    for path in (root/'Solutions').glob('**/*.lean'):
        if path.name == 'TutoLib.lean':
            continue
        print(path)
        out = root/'Exercises'/path.relative_to(root/'Solutions')
        with out.open('w') as outp:
            with path.open() as inp:
                state = 'normal'
                for line in inp:
                    m = sorry_regex.match(line)
                    if state == 'normal':
                        if m:
                            state = 'sorry'
                        else:
                            outp.write(line)
                    else:
                        if m:
                            state = 'normal'
                            outp.write(m.group(1)+ 'sorry\n')

            outp.write('\n')



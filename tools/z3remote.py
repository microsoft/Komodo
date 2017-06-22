#!/usr/bin/env python3

import sys, os, subprocess, gzip, json, codecs

DEFAULT_ARGS = ['AUTO_CONFIG=false', '-smt2', '-in']

def main(args):
    ret = {}

    with codecs.getreader('utf-8')(gzip.open(sys.stdin.buffer, mode='rb')) as gzin, \
        subprocess.Popen(['z3'] + DEFAULT_ARGS + args,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          universal_newlines=True) as p:

        # decompress the query into stdin
        while True:
            buf = gzin.read(64*1024)
            if buf:
                p.stdin.write(buf)
            else:
                break
        p.stdin.write('(check-sat)\n')
        p.stdin.flush()

        # read the response
        res = p.stdout.readline().strip()
        ret['result'] = res

        if res == 'unknown':
            p.stdin.write('(get-info :reason-unknown)\n')
            p.stdin.flush()
            ret['reasonunknown'] = p.stdout.readline().strip()

        if res != 'unsat':
            p.stdin.write('(labels)\n')
            p.stdin.flush()
            ret['labels'] = p.stdout.readline().strip()

        p.kill()

    json.dump(ret, sys.stdout)

if __name__ == '__main__':
    main(sys.argv[1:])

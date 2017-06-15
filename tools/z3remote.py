#!/usr/bin/env python3

import sys, os, json, io, gzip, random, time
import requests # pip3 install requests

LOGFILE='z3remote.log'
NAME_RESPONSE = '(:name "Z3")'
API_URL = 'https://komverify.azurewebsites.net/api/z3'
HTTP_HEADERS = {'Content-Type': 'application/octet-stream'}
API_KEY_ENVVAR = 'Z3REMOTEKEY'

def do_query(log, session, apikey, query, extra_args=None):
    bio = io.BytesIO()
    g = gzip.GzipFile(fileobj=bio, mode='wb')
    g.write(query.encode('utf-8'))
    g.close()

    params = {'code': apikey}
    if extra_args:
        params['args'] = extra_args

    # cheesy attempt at a load balancer! (which doesn't really work)
    #time.sleep(random.uniform(1, 30.0))

    start = time.time()
    req = session.post(API_URL, params=params, data=bio.getvalue(), headers=HTTP_HEADERS)
    req.raise_for_status()
    resp = req.json()
    stop = time.time()
    log.write('%dkB query took %fs\n' % (len(query) / 1024, stop - start))

    sys.stdout.write(resp['result'])
    sys.stdout.flush()

    for line in sys.stdin:
        if line.strip() == '(get-info :name)':
            sys.stdout.write(NAME_RESPONSE + '\n')
            sys.stdout.flush()
        elif line.strip() == '(get-info :reason-unknown)':
            sys.stdout.write(resp['reasonunknown'])
            sys.stdout.flush()
        elif line.strip() == '(labels)':
            sys.stdout.write(resp['labels'])
            sys.stdout.flush()
        elif line.strip() == '(reset)':
            break
        else:
            pass #log.write('IGN: ' + line)


def main(args):
    try:
        apikey = os.environ[API_KEY_ENVVAR]
    except KeyError:
        sys.stderr.write('Error: %s must be set in the environment\n' % API_KEY_ENVVAR)
        return 1

    if args == ['--version']:
        sys.stdout.write('Z3 version 4.5.0 - 64 bit\n')
        return 0
    elif args[:3] != ['AUTO_CONFIG=false', '-smt2', '-in']:
        sys.stderr.write('Error: unsupported Z3 args: %s\n' % ' '.join(args))
        return 1

    log = open(LOGFILE, 'a')
    log.write('NEW: ' + ' '.join(args) + '\n')

    session = requests.Session()
    extra_args = args[3:] if len(args) > 3 else None
    query = ''

    for line in sys.stdin:
        #log.write('IN: ' + line)
        if line.strip() == '(get-info :name)':
            sys.stdout.write(NAME_RESPONSE + '\n')
            sys.stdout.flush()
        else:
            query = query + line
            if line.strip() == '(check-sat)':
                do_query(log, session, apikey, query, extra_args)
                query = ''

    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

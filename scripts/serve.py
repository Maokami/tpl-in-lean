#!/usr/bin/env python3
"""Verso 가 만든 HTML 을 로컬에서 띄운다.

파일로 직접 열면 코드 호버가 깨진다 — 일부 내용이 JSON 으로 분리되어
fetch 로 불러오기 때문이다. 그리고 기본 http.server 는 캐시 헤더 때문에
내용이 갱신되지 않는 일이 있어서, 캐시를 끄는 헤더를 붙인다.

    python3 scripts/serve.py 8000 -d manual/_out/html-multi
"""
import argparse
import functools
import http.server


class NoCacheHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store, must-revalidate")
        self.send_header("Expires", "0")
        super().end_headers()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("port", nargs="?", type=int, default=8000)
    p.add_argument("-d", "--directory", default=".")
    args = p.parse_args()
    handler = functools.partial(NoCacheHandler, directory=args.directory)
    with http.server.ThreadingHTTPServer(("127.0.0.1", args.port), handler) as httpd:
        print(f"http://127.0.0.1:{args.port} 에서 {args.directory} 를 서빙한다. Ctrl-C 로 종료.")
        httpd.serve_forever()


if __name__ == "__main__":
    main()

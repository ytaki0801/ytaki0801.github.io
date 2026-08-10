<?php

/*
 * nip05.php
 *
 * NIP-05 → Nostrプロフィール表示
 *
 * 使用例:
 *
 *   https://example.com/nip05.php?id=user@domain.com
 *
 * 対応:
 *
 *   ?id=user@domain.com
 *   ?id=_@domain.com
 *   ?id=domain.com
 *
 * Composer不要
 * 外部PHPライブラリ不要
 */


// ==================================================
// 設定
// ==================================================

$BOOTSTRAP_RELAYS = [
    "wss://relay.damus.io",
    "wss://nos.lol",
    "wss://relay.primal.net",
    "wss://relay.snort.social"
];

$TIMEOUT = 8;


// ==================================================
// HTMLエスケープ
// ==================================================

function h($value)
{
    return htmlspecialchars(
        (string)$value,
        ENT_QUOTES | ENT_SUBSTITUTE,
        "UTF-8"
    );
}


// ==================================================
// NIP-05入力の正規化
// ==================================================

function normalize_nip05($value)
{
    $value = trim($value);

    if (substr($value, 0, 8) === "https://") {
        $value = substr($value, 8);
    }
    elseif (substr($value, 0, 7) === "http://") {
        $value = substr($value, 7);
    }

    $value = rtrim($value, "/");

    /*
     * domain.com
     *     ↓
     * _@domain.com
     */
    if (strpos($value, "@") === false) {
        $value = "_@" . $value;
    }

    return $value;
}


// ==================================================
// 表示用NIP-05
// ==================================================

function display_nip05($value)
{
    if (!$value) {
        return "";
    }

    $value = trim($value);

    if (substr($value, 0, 8) === "https://") {
        $value = substr($value, 8);
    }
    elseif (substr($value, 0, 7) === "http://") {
        $value = substr($value, 7);
    }

    $value = rtrim($value, "/");

    /*
     * _@domain.com
     *     ↓
     * domain.com
     */
    if (substr($value, 0, 2) === "_@") {
        return substr($value, 2);
    }

    /*
     * @domain.com
     *     ↓
     * domain.com
     */
    if (substr($value, 0, 1) === "@") {
        return substr($value, 1);
    }

    return $value;
}


// ==================================================
// NIP-05 → 公開鍵HEX
// ==================================================

function nip05_to_hex_pubkey($nip05)
{
    $nip05 = normalize_nip05($nip05);

    if (strpos($nip05, "@") === false) {
        throw new Exception(
            "NIP-05形式ではありません。"
        );
    }

    [$name, $domain] =
        explode("@", $nip05, 2);

    if ($name === "") {
        $name = "_";
    }

    if ($domain === "") {
        throw new Exception(
            "ドメインが指定されていません。"
        );
    }

    /*
     * NIP-05 username:
     *
     * [a-z0-9-_.]+
     */
    if (
        !preg_match(
            '/^[a-zA-Z0-9._-]+$/',
            $name
        )
    ) {
        throw new Exception(
            "NIP-05ユーザー名に使用できない文字が含まれています。"
        );
    }

    /*
     * ドメインとして最低限の形式を確認
     */
    if (
        !preg_match(
            '/^[a-zA-Z0-9.-]+$/',
            $domain
        )
    ) {
        throw new Exception(
            "ドメインの形式が不正です。"
        );
    }

    /*
     * NIP-05:
     *
     * https://domain/.well-known/nostr.json?name=name
     */
    $url =
        "https://" .
        $domain .
        "/.well-known/nostr.json?name=" .
        rawurlencode($name);

    $context =
        stream_context_create([
            "http" => [
                "timeout" => 10,
                "method" => "GET",
                "header" =>
                    "User-Agent: NostrProfileWeb/1.0\r\n"
            ]
        ]);

    $json =
        @file_get_contents(
            $url,
            false,
            $context
        );

    if ($json === false) {
        throw new Exception(
            "NIP-05情報を取得できませんでした。"
        );
    }

    $data =
        json_decode(
            $json,
            true
        );

    if (!is_array($data)) {
        throw new Exception(
            "nostr.jsonを解析できませんでした。"
        );
    }

    if (
        !isset($data["names"]) ||
        !is_array($data["names"])
    ) {
        throw new Exception(
            "nostr.jsonにnamesがありません。"
        );
    }

    if (
        !isset($data["names"][$name])
    ) {
        throw new Exception(
            "NIP-05ユーザーが見つかりません。"
        );
    }

    $pubkey =
        $data["names"][$name];

    /*
     * 32 byte = 64 hex characters
     */
    if (
        !is_string($pubkey) ||
        strlen($pubkey) !== 64 ||
        !ctype_xdigit($pubkey)
    ) {
        throw new Exception(
            "公開鍵が正しい64文字のHEXではありません。"
        );
    }

    return [
        "nip05" =>
            $nip05,

        "pubkey" =>
            strtolower($pubkey)
    ];
}


// ==================================================
// 8bit → 5bit
// ==================================================

function convert_bits_8_to_5($data)
{
    $acc = 0;
    $bits = 0;
    $ret = [];

    for (
        $i = 0;
        $i < strlen($data);
        $i++
    ) {
        $value = ord($data[$i]);

        $acc =
            ($acc << 8) |
            $value;

        $bits += 8;

        while ($bits >= 5) {

            $bits -= 5;

            $ret[] =
                ($acc >> $bits) & 31;
        }
    }

    if ($bits > 0) {

        $ret[] =
            ($acc << (5 - $bits)) & 31;
    }

    return $ret;
}


// ==================================================
// Bech32 polymod
// ==================================================

function bech32_polymod($values)
{
    $generator = [
        0x3b6a57b2,
        0x26508e6d,
        0x1ea119fa,
        0x3d4233dd,
        0x2a1462b3
    ];

    $chk = 1;

    foreach ($values as $value) {

        $top = $chk >> 25;

        $chk =
            (($chk & 0x1ffffff) << 5)
            ^ $value;

        for (
            $i = 0;
            $i < 5;
            $i++
        ) {

            if (
                (($top >> $i) & 1) !== 0
            ) {
                $chk ^=
                    $generator[$i];
            }
        }
    }

    return $chk;
}


// ==================================================
// Bech32 HRP expand
// ==================================================

function bech32_hrp_expand($hrp)
{
    $ret = [];

    for (
        $i = 0;
        $i < strlen($hrp);
        $i++
    ) {

        $ret[] =
            ord($hrp[$i]) >> 5;
    }

    $ret[] = 0;

    for (
        $i = 0;
        $i < strlen($hrp);
        $i++
    ) {

        $ret[] =
            ord($hrp[$i]) & 31;
    }

    return $ret;
}


// ==================================================
// HEX公開鍵 → npub
// ==================================================

function hex_to_npub($hex)
{
    $data =
        hex2bin($hex);

    if ($data === false) {
        throw new Exception(
            "公開鍵HEXを変換できません。"
        );
    }

    $converted =
        convert_bits_8_to_5($data);

    $hrp = "npub";

    $values =
        array_merge(
            bech32_hrp_expand($hrp),
            $converted,
            [0, 0, 0, 0, 0, 0]
        );

    $polymod =
        bech32_polymod($values) ^ 1;

    $checksum = [];

    for (
        $i = 0;
        $i < 6;
        $i++
    ) {

        $shift =
            5 * (5 - $i);

        $checksum[] =
            ($polymod >> $shift) & 31;
    }

    $charset =
        "qpzry9x8gf2tvdw0s3jn54khce6mua7l";

    $result =
        "npub1";

    foreach (
        array_merge(
            $converted,
            $checksum
        ) as $value
    ) {

        $result .=
            $charset[$value];
    }

    return $result;
}


// ==================================================
// WebSocket URL解析
// ==================================================

function parse_ws_url($url)
{
    $parts =
        parse_url($url);

    if (
        $parts === false ||
        !isset($parts["scheme"]) ||
        !isset($parts["host"])
    ) {
        throw new Exception(
            "WebSocket URLが不正です。"
        );
    }

    $scheme =
        strtolower(
            $parts["scheme"]
        );

    if (
        $scheme !== "wss" &&
        $scheme !== "ws"
    ) {
        throw new Exception(
            "wss:// または ws:// が必要です。"
        );
    }

    $host =
        $parts["host"];

    $port =
        $parts["port"]
        ??
        (
            $scheme === "wss"
            ? 443
            : 80
        );

    $path =
        $parts["path"]
        ??
        "/";

    if (
        isset($parts["query"]) &&
        $parts["query"] !== ""
    ) {

        $path .=
            "?" .
            $parts["query"];
    }

    return [
        "scheme" => $scheme,
        "host"   => $host,
        "port"   => $port,
        "path"   => $path
    ];
}


// ==================================================
// WebSocket接続
// ==================================================

function websocket_connect(
    $url,
    $timeout
) {
    $parts =
        parse_ws_url($url);

    $host =
        $parts["host"];

    $port =
        $parts["port"];

    $transport =
        ($parts["scheme"] === "wss")
        ? "ssl://"
        : "tcp://";

    $context =
        stream_context_create([
            "ssl" => [
                "verify_peer" =>
                    true,

                "verify_peer_name" =>
                    true,

                "allow_self_signed" =>
                    false,

                "peer_name" =>
                    $host
            ]
        ]);

    $errno = 0;
    $errstr = "";

    $socket =
        @stream_socket_client(
            $transport .
            $host .
            ":" .
            $port,
            $errno,
            $errstr,
            $timeout,
            STREAM_CLIENT_CONNECT,
            $context
        );

    if ($socket === false) {

        throw new Exception(
            "Relayへの接続に失敗しました。"
        );
    }

    stream_set_timeout(
        $socket,
        $timeout
    );

    /*
     * WebSocket handshake
     */
    $key =
        base64_encode(
            random_bytes(16)
        );

    $request =
        "GET " .
        $parts["path"] .
        " HTTP/1.1\r\n" .
        "Host: " .
        $host .
        ":" .
        $port .
        "\r\n" .
        "Upgrade: websocket\r\n" .
        "Connection: Upgrade\r\n" .
        "Sec-WebSocket-Key: " .
        $key .
        "\r\n" .
        "Sec-WebSocket-Version: 13\r\n" .
        "User-Agent: NostrProfileWeb/1.0\r\n" .
        "\r\n";

    fwrite(
        $socket,
        $request
    );

    /*
     * HTTP response
     */
    $response = "";

    while (
        strpos(
            $response,
            "\r\n\r\n"
        ) === false
    ) {

        $chunk =
            fread(
                $socket,
                4096
            );

        if (
            $chunk === false ||
            $chunk === ""
        ) {

            fclose($socket);

            throw new Exception(
                "WebSocketハンドシェイクに失敗しました。"
            );
        }

        $response .=
            $chunk;

        if (
            strlen($response) > 65536
        ) {

            fclose($socket);

            throw new Exception(
                "WebSocket応答が大きすぎます。"
            );
        }
    }

    $header_end =
        strpos(
            $response,
            "\r\n\r\n"
        );

    $headers =
        substr(
            $response,
            0,
            $header_end
        );

    /*
     * 101 Switching Protocols
     */
    if (
        !preg_match(
            '#^HTTP/\d+\.\d+\s+101\b#i',
            $headers
        )
    ) {

        fclose($socket);

        throw new Exception(
            "101 Switching Protocolsが返されませんでした。"
        );
    }

    /*
     * Sec-WebSocket-Accept
     */
    $expected_accept =
        base64_encode(
            sha1(
                $key .
                "258EAFA5-E914-47DA-95CA-C5AB0DC85B11",
                true
            )
        );

    $actual_accept = null;

    if (
        preg_match(
            '/^Sec-WebSocket-Accept:\s*(.+)$/im',
            $headers,
            $matches
        )
    ) {

        $actual_accept =
            trim($matches[1]);
    }

    if (
        $actual_accept === null ||
        !hash_equals(
            $expected_accept,
            $actual_accept
        )
    ) {

        fclose($socket);

        throw new Exception(
            "WebSocketハンドシェイクの検証に失敗しました。"
        );
    }

    return $socket;
}


// ==================================================
// 指定バイト数読み込み
// ==================================================

function websocket_read_bytes(
    $socket,
    $length,
    $timeout
) {
    $data = "";

    while (
        strlen($data) < $length
    ) {

        $read = [$socket];
        $write = null;
        $except = null;

        $changed =
            stream_select(
                $read,
                $write,
                $except,
                $timeout,
                0
            );

        if ($changed === false) {

            throw new Exception(
                "WebSocket読み込み待機に失敗しました。"
            );
        }

        if ($changed === 0) {

            throw new Exception(
                "WebSocket受信がタイムアウトしました。"
            );
        }

        $chunk =
            fread(
                $socket,
                $length - strlen($data)
            );

        if (
            $chunk === false ||
            $chunk === ""
        ) {

            throw new Exception(
                "WebSocket接続が切断されました。"
            );
        }

        $data .=
            $chunk;
    }

    return $data;
}


// ==================================================
// WebSocketフレーム送信
// ==================================================

function websocket_send(
    $socket,
    $payload,
    $opcode = 0x1
) {
    $length =
        strlen($payload);

    $first =
        0x80 |
        ($opcode & 0x0f);

    /*
     * クライアント→サーバーはMASK必須
     */
    $mask =
        random_bytes(4);

    $frame =
        chr($first);

    if ($length < 126) {

        $frame .=
            chr(0x80 | $length);
    }
    elseif ($length <= 0xffff) {

        $frame .=
            chr(0x80 | 126);

        $frame .=
            pack("n", $length);
    }
    else {

        $frame .=
            chr(0x80 | 127);

        $high =
            intdiv(
                $length,
                4294967296
            );

        $low =
            $length % 4294967296;

        $frame .=
            pack(
                "NN",
                $high,
                $low
            );
    }

    $masked = "";

    for (
        $i = 0;
        $i < $length;
        $i++
    ) {

        $masked .=
            $payload[$i]
            ^
            $mask[$i % 4];
    }

    $frame .=
        $mask .
        $masked;

    $written = 0;

    $frame_length =
        strlen($frame);

    while (
        $written < $frame_length
    ) {

        $n =
            fwrite(
                $socket,
                substr(
                    $frame,
                    $written
                )
            );

        if (
            $n === false ||
            $n === 0
        ) {

            throw new Exception(
                "WebSocketフレーム送信に失敗しました。"
            );
        }

        $written +=
            $n;
    }
}


// ==================================================
// WebSocketフレーム受信
// ==================================================

function websocket_receive_frame(
    $socket,
    $timeout
) {
    $header =
        websocket_read_bytes(
            $socket,
            2,
            $timeout
        );

    $byte1 =
        ord($header[0]);

    $byte2 =
        ord($header[1]);

    $fin =
        (($byte1 & 0x80) !== 0);

    $opcode =
        $byte1 & 0x0f;

    $masked =
        (($byte2 & 0x80) !== 0);

    $length =
        $byte2 & 0x7f;

    if ($length === 126) {

        $extended =
            websocket_read_bytes(
                $socket,
                2,
                $timeout
            );

        $length =
            unpack(
                "n",
                $extended
            )[1];
    }
    elseif ($length === 127) {

        $extended =
            websocket_read_bytes(
                $socket,
                8,
                $timeout
            );

        $parts =
            unpack(
                "Nhigh/Nlow",
                $extended
            );

        $length =
            $parts["high"]
            * 4294967296
            +
            $parts["low"];
    }

    if (
        $opcode >= 0x8 &&
        $length > 125
    ) {

        throw new Exception(
            "不正なWebSocket制御フレームです。"
        );
    }

    $mask_key = "";

    if ($masked) {

        $mask_key =
            websocket_read_bytes(
                $socket,
                4,
                $timeout
            );
    }

    $payload = "";

    if ($length > 0) {

        $payload =
            websocket_read_bytes(
                $socket,
                $length,
                $timeout
            );
    }

    if ($masked) {

        $unmasked = "";

        for (
            $i = 0;
            $i < $length;
            $i++
        ) {

            $unmasked .=
                $payload[$i]
                ^
                $mask_key[$i % 4];
        }

        $payload =
            $unmasked;
    }

    return [
        "fin" =>
            $fin,

        "opcode" =>
            $opcode,

        "payload" =>
            $payload
    ];
}


// ==================================================
// WebSocketメッセージ受信
// ==================================================

function websocket_receive_message(
    $socket,
    $timeout
) {
    $message = "";
    $fragmented = false;

    while (true) {

        $frame =
            websocket_receive_frame(
                $socket,
                $timeout
            );

        $opcode =
            $frame["opcode"];

        /*
         * TEXT
         */
        if ($opcode === 0x1) {

            $message =
                $frame["payload"];

            if ($frame["fin"]) {
                return $message;
            }

            $fragmented = true;

            continue;
        }

        /*
         * CONTINUATION
         */
        if ($opcode === 0x0) {

            if (!$fragmented) {
                continue;
            }

            $message .=
                $frame["payload"];

            if ($frame["fin"]) {
                return $message;
            }

            continue;
        }

        /*
         * CLOSE
         */
        if ($opcode === 0x8) {

            try {

                websocket_send(
                    $socket,
                    $frame["payload"],
                    0x8
                );

            }
            catch (Throwable $e) {
            }

            return null;
        }

        /*
         * PING
         */
        if ($opcode === 0x9) {

            websocket_send(
                $socket,
                $frame["payload"],
                0xA
            );

            continue;
        }

        /*
         * PONG
         */
        if ($opcode === 0xA) {
            continue;
        }
    }
}


// ==================================================
// WebSocket終了
// ==================================================

function websocket_close($socket)
{
    if (is_resource($socket)) {

        try {

            websocket_send(
                $socket,
                pack("n", 1000),
                0x8
            );

        }
        catch (Throwable $e) {
        }

        fclose($socket);
    }
}


// ==================================================
// Nostr Relayからイベント取得
// ==================================================

function query_event(
    $relay_url,
    $pubkey_hex,
    $kind,
    $timeout
) {
    $socket = null;

    try {

        $socket =
            websocket_connect(
                $relay_url,
                $timeout
            );

        $subscription_id =
            bin2hex(
                random_bytes(8)
            );

        $request = [
            "REQ",
            $subscription_id,
            [
                "authors" => [
                    $pubkey_hex
                ],

                "kinds" => [
                    $kind
                ],

                "limit" => 1
            ]
        ];

        websocket_send(
            $socket,
            json_encode(
                $request,
                JSON_UNESCAPED_SLASHES
            )
        );

        $newest_event = null;

        while (true) {

            $raw =
                websocket_receive_message(
                    $socket,
                    $timeout
                );

            if ($raw === null) {
                break;
            }

            $message =
                json_decode(
                    $raw,
                    true
                );

            if (
                !is_array($message) ||
                count($message) === 0
            ) {
                continue;
            }

            $type =
                $message[0];

            /*
             * EVENT
             */
            if (
                $type === "EVENT" &&
                count($message) >= 3
            ) {

                $event =
                    $message[2];

                if (
                    isset(
                        $event["created_at"]
                    )
                ) {

                    if (
                        $newest_event === null ||
                        $event["created_at"]
                        >
                        $newest_event["created_at"]
                    ) {

                        $newest_event =
                            $event;
                    }
                }
            }

            /*
             * EOSE
             */
            elseif (
                $type === "EOSE"
            ) {
                break;
            }

            /*
             * CLOSED
             */
            elseif (
                $type === "CLOSED"
            ) {
                break;
            }
        }

        websocket_close(
            $socket
        );

        return $newest_event;

    }
    catch (Throwable $e) {

        if ($socket !== null) {
            websocket_close(
                $socket
            );
        }

        return null;
    }
}


// ==================================================
// NIP-65 Kind 10002
// ==================================================

function fetch_relay_list(
    $pubkey_hex,
    $bootstrap_relays,
    $timeout
) {
    $newest_event = null;

    foreach (
        $bootstrap_relays as $relay
    ) {

        $event =
            query_event(
                $relay,
                $pubkey_hex,
                10002,
                $timeout
            );

        if ($event === null) {
            continue;
        }

        if (
            $newest_event === null ||
            $event["created_at"]
            >
            $newest_event["created_at"]
        ) {

            $newest_event =
                $event;
        }
    }

    /*
     * NIP-65が取得できなかった場合
     */
    if ($newest_event === null) {
        return $bootstrap_relays;
    }

    $write_relays = [];
    $all_relays = [];

    foreach (
        $newest_event["tags"] ?? []
        as $tag
    ) {

        if (
            count($tag) < 2 ||
            $tag[0] !== "r"
        ) {
            continue;
        }

        $relay =
            $tag[1];

        if (
            substr(
                $relay,
                0,
                6
            ) !== "wss://"
        ) {
            continue;
        }

        $mode = null;

        if (count($tag) >= 3) {
            $mode = $tag[2];
        }

        $all_relays[] =
            $relay;

        /*
         * modeなし = read/write
         * write = write
         */
        if (
            $mode === "write" ||
            $mode === null
        ) {

            $write_relays[] =
                $relay;
        }
    }

    $write_relays =
        array_values(
            array_unique(
                $write_relays
            )
        );

    $all_relays =
        array_values(
            array_unique(
                $all_relays
            )
        );

    if (
        count($write_relays) > 0
    ) {
        return $write_relays;
    }

    if (
        count($all_relays) > 0
    ) {
        return $all_relays;
    }

    return $bootstrap_relays;
}


// ==================================================
// Kind 0 Profile
// ==================================================

function fetch_profile(
    $pubkey_hex,
    $relays,
    $timeout
) {
    $newest_event = null;

    foreach (
        $relays as $relay
    ) {

        $event =
            query_event(
                $relay,
                $pubkey_hex,
                0,
                $timeout
            );

        if ($event === null) {
            continue;
        }

        if (
            $newest_event === null ||
            $event["created_at"]
            >
            $newest_event["created_at"]
        ) {

            $newest_event =
                $event;
        }
    }

    if ($newest_event === null) {

        throw new Exception(
            "Kind 0プロフィールを取得できませんでした。"
        );
    }

    $profile =
        json_decode(
            $newest_event["content"],
            true
        );

    if (!is_array($profile)) {

        throw new Exception(
            "Kind 0のcontentをJSONとして解析できません。"
        );
    }

    return $profile;
}


// ==================================================
// プロフィール値を表示用文字列へ変換
// ==================================================

function profile_value_to_string(
    $key,
    $value
) {
    /*
     * nip05だけ簡易表示
     */
    if (
        $key === "nip05" &&
        is_string($value)
    ) {

        return display_nip05(
            $value
        );
    }

    /*
     * 配列・オブジェクト
     */
    if (
        is_array($value) ||
        is_object($value)
    ) {

        return json_encode(
            $value,
            JSON_UNESCAPED_UNICODE |
            JSON_UNESCAPED_SLASHES
        );
    }

    /*
     * null
     */
    if ($value === null) {
        return "";
    }

    /*
     * boolean
     */
    if (is_bool($value)) {

        return $value
            ? "true"
            : "false";
    }

    return (string)$value;
}


// ==================================================
// プロフィール表示
// ==================================================

function print_profile(
    $profile,
    $npub
) {
    echo '<div class="profile">' . "\n";

    echo '<h1>Nostr Profile</h1>' . "\n";

    /*
     * npub
     */
    echo '<div class="profile-row">' . "\n";

    echo '<div class="profile-key">npub</div>';

    echo '<div class="profile-value">'
        . h($npub)
        . '</div>';

    echo "</div>\n";


    /*
     * Kind 0プロフィールJSONに
     * 含まれている全キー・全値を表示
     */
    foreach (
        $profile as $key => $value
    ) {

        $value =
            profile_value_to_string(
                $key,
                $value
            );

        /*
         * 空の値は項目自体を表示しない
         */
        if (
            trim($value) === ""
        ) {
            continue;
        }

        echo '<div class="profile-row">' . "\n";

        echo '<div class="profile-key">'
            . h($key)
            . '</div>';

        echo '<div class="profile-value">'
            . h($value)
            . '</div>';

        echo "</div>\n";
    }

    echo "</div>\n";
}


// ==================================================
// HTML開始
// ==================================================

header(
    "Content-Type: text/html; charset=UTF-8"
);

?>
<!DOCTYPE html>
<html lang="ja">

<head>

<meta charset="UTF-8">

<meta name="viewport"
      content="width=device-width, initial-scale=1.0">

<title>Nostr Profile</title>

<style>

body {
    font-family:
        -apple-system,
        BlinkMacSystemFont,
        "Segoe UI",
        sans-serif;

    margin: 30px;

    background: #f5f5f5;

    color: #222;
}

.profile {
    max-width: 900px;

    margin: 0 auto;

    background: #fff;

    border: 1px solid #ddd;

    border-radius: 8px;

    padding: 20px;
}

.profile h1 {
    font-size: 24px;

    margin-top: 0;

    margin-bottom: 20px;
}

.profile-row {
    display: grid;

    grid-template-columns:
        140px 1fr;

    border-top: 1px solid #eee;

    padding: 10px 0;

    word-break: break-word;
}

.profile-key {
    font-weight: bold;

    color: #555;
}

.profile-value {
    color: #222;

    white-space: pre-wrap;
}

.error {
    max-width: 900px;

    margin: 30px auto;

    padding: 20px;

    background: #fff;

    border: 1px solid #d88;

    border-radius: 8px;

    color: #900;
}

@media (
    max-width: 600px
) {

    body {
        margin: 10px;
    }

    .profile-row {
        grid-template-columns:
            1fr;
    }

    .profile-key {
        margin-bottom: 4px;
    }
}

</style>

</head>

<body>

<?php

// ==================================================
// Main
// ==================================================

try {

    /*
     * GETパラメータ
     *
     * nip05.php?id=user@domain.com
     */
    if (
        !isset($_GET["id"])
    ) {

        throw new Exception(
            "idパラメータが指定されていません。"
        );
    }

    $user_input =
        trim(
            $_GET["id"]
        );

    if (
        $user_input === ""
    ) {

        throw new Exception(
            "idパラメータが空です。"
        );
    }


    /*
     * NIP-05
     * ↓
     * 公開鍵HEX
     */
    $result =
        nip05_to_hex_pubkey(
            $user_input
        );

    $pubkey_hex =
        $result["pubkey"];


    /*
     * 公開鍵HEX
     * ↓
     * npub
     */
    $npub =
        hex_to_npub(
            $pubkey_hex
        );


    /*
     * NIP-65
     * ↓
     * Relay List
     */
    $relays =
        fetch_relay_list(
            $pubkey_hex,
            $BOOTSTRAP_RELAYS,
            $TIMEOUT
        );


    /*
     * Kind 0
     * ↓
     * Profile JSON
     */
    $profile =
        fetch_profile(
            $pubkey_hex,
            $relays,
            $TIMEOUT
        );


    /*
     * 表示
     */
    print_profile(
        $profile,
        $npub
    );

}
catch (Throwable $e) {

    echo '<div class="error">' . "\n";

    echo '<h1>エラー</h1>' . "\n";

    echo '<p>'
        . nl2br(
            h($e->getMessage())
        )
        . '</p>' . "\n";

    echo "</div>\n";
}

?>

</body>

</html>

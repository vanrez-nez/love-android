package org.love2d.android.ble;

import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothGatt;
import android.bluetooth.BluetoothGattCallback;
import android.bluetooth.BluetoothGattCharacteristic;
import android.bluetooth.BluetoothGattDescriptor;
import android.bluetooth.BluetoothGattServer;
import android.bluetooth.BluetoothGattServerCallback;
import android.bluetooth.BluetoothGattService;
import android.bluetooth.BluetoothManager;
import android.bluetooth.BluetoothProfile;
import android.bluetooth.le.AdvertiseCallback;
import android.bluetooth.le.AdvertiseData;
import android.bluetooth.le.AdvertiseSettings;
import android.bluetooth.le.BluetoothLeAdvertiser;
import android.bluetooth.le.BluetoothLeScanner;
import android.bluetooth.le.ScanCallback;
import android.bluetooth.le.ScanRecord;
import android.bluetooth.le.ScanResult;
import android.bluetooth.le.ScanSettings;
import android.Manifest;
import android.app.Activity;
import android.content.Context;
import android.content.pm.PackageManager;
import android.os.Build;
import android.os.Handler;
import android.os.Looper;
import android.os.ParcelUuid;
import android.util.Log;

import androidx.annotation.Keep;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.zip.CRC32;

/**
 * BLE Game Network Protocol v2.0.0 — Android implementation.
 *
 * Phase 2: GATT server/client, packet encoding/decoding, fragmentation/reassembly,
 * connection lifecycle, handshake, roster management, dedup, write serialization,
 * heartbeat, reconnect grace, message routing.
 *
 * Called from C++ via JNI.
 */
@Keep
public class BleManager {

    private static final String TAG = "LoveBLE";

    // ── Protocol UUIDs (spec Section 2) ──

    private static final UUID SERVICE_UUID =
            UUID.fromString("4bdf6b6d-6b77-4b3f-9f4a-5a2d1499d641");
    private static final UUID CHARACTERISTIC_UUID =
            UUID.fromString("9e153f71-c2d0-4ee1-8b8d-090421bea607");
    private static final UUID CCCD_UUID =
            UUID.fromString("00002902-0000-1000-8000-00805f9b34fb");

    // Manufacturer company ID for advertisement (spec Section 3.3)
    private static final int MANUFACTURER_COMPANY_ID = 0xFFFF;

    // ── Protocol constants (spec Section 17) ──

    private static final byte PROTOCOL_VERSION = 1;         // packet/fragment envelope version (always 1)
    private static final int CURRENT_PROTOCOL_VERSION = 4;  // application-level protocol version (spec Section 3.1)
    private static final int DESIRED_MTU = 185;
    private static final int DEFAULT_MTU = 23;
    private static final int ATT_OVERHEAD = 3;
    private static final int FRAGMENT_HEADER_SIZE = 5;
    private static final int MAX_STRING_LENGTH = 4096;
    private static final int MAX_PAYLOAD_LENGTH = 65536;

    // Timeouts (spec Section 17)
    private static final long HEARTBEAT_INTERVAL_MS = 2000;
    private static final long ASSEMBLY_TIMEOUT_MS = 15000;
    private static final long PENDING_CLIENT_TIMEOUT_MS = 5000;
    private static final long RECONNECT_TIMEOUT_MS = 10000;
    private static final long DEPARTURE_SEND_TIMEOUT_MS = 100;
    private static final long DEPARTURE_INTENT_EXPIRY_MS = 2000;
    private static final long DEDUP_EXPIRY_MS = 5000;
    private static final int DEDUP_WINDOW = 64;
    private static final long ROOM_EXPIRY_MS = 4000;
    private static final long ROOM_EXPIRY_CHECK_MS = 1000;
    private static final int MAX_CONCURRENT_ASSEMBLIES_PER_SOURCE = 32;
    private static final long MIGRATION_DEPARTURE_DELAY_MS = 400;
    private static final long MIGRATION_TIMEOUT_MS = 3000;
    private static final long RECOVERY_HOST_PROBE_DURATION_MS = 1500; // spec Section 8.2

    // ── Core references ──

    private final Context context;
    private final Handler handler;
    private final BluetoothManager bluetoothManager;
    private final BluetoothAdapter bluetoothAdapter;

    // Local identity
    private final String localPeerId;

    // ── Nonce and MessageID counters (spec Section 5.3 and 4.1) ──

    private int nonceCounter = 0;   // 16-bit, wraps 65535->1, 0 reserved
    private int messageIdCounter = 0; // 16-bit, same wrapping

    // ── Host state ──

    private boolean hosting = false;
    private String sessionId;
    private String roomName;
    private int maxClients;
    private char transportChar;
    private int peerCount = 0;
    private int membershipEpoch = 0;
    private BluetoothGattServer gattServer;
    private BluetoothGattCharacteristic messageCharacteristic;
    private BluetoothLeAdvertiser advertiser;
    private AdvertiseCallback advertiseCallback;
    private boolean hostServiceReady = false;

    // Host: connected clients map (peerId -> BluetoothDevice)
    private final HashMap<String, BluetoothDevice> connectedClients = new HashMap<>();
    // Host: device-peer map (device address -> peerId)
    private final HashMap<String, String> devicePeerMap = new HashMap<>();
    // Host: pending clients (device address -> timestamp ms)
    private final HashMap<String, Long> pendingClients = new HashMap<>();
    // Host: per-device notification queues (device address -> queue)
    private final HashMap<String, LinkedList<byte[]>> notificationQueues = new HashMap<>();
    // Host: per-device notification in-flight flag
    private final HashSet<String> notificationInFlight = new HashSet<>();
    // Host: per-device MTU map (device address -> MTU value)
    private final HashMap<String, Integer> deviceMTUs = new HashMap<>();
    // Host: subscribed centrals (device addresses)
    private final HashSet<String> subscribedCentrals = new HashSet<>();
    // Host: recent departure intents (peerId -> timestamp ms)
    private final HashMap<String, Long> departureIntents = new HashMap<>();

    // ── Client state ──

    private boolean clientJoined = false;
    private boolean clientLeaving = false;
    private String joinedRoomId;
    private String joinedSessionId;
    private String hostPeerId;
    private BluetoothGatt clientGatt;
    private BluetoothGattCharacteristic remoteCharacteristic;
    private int negotiatedMTU = DEFAULT_MTU;

    // Client: write queue (spec Section 15.1)
    private final LinkedList<byte[]> clientWriteQueue = new LinkedList<>();
    private boolean writeInFlight = false;
    private final LinkedList<byte[]> departureWriteFragments = new LinkedList<>();
    private boolean departureSendInProgress = false;
    private Runnable departureSendTimeoutRunnable;

    // ── Scan state ──

    private boolean scanning = false;
    private BluetoothLeScanner scanner;
    private ScanCallback scanCallback;
    private final HashMap<String, RoomInfo> discoveredRooms = new HashMap<>();
    private Runnable roomExpiryRunnable;

    // ── Session peers roster ──

    private final ArrayList<SessionPeer> sessionPeers = new ArrayList<>();

    // ── Fragment assembler: sourceKey -> (assemblyKey -> InboundAssembly) ──

    private final HashMap<String, HashMap<String, InboundAssembly>> assemblerBySource = new HashMap<>();

    // ── Dedup state (spec Section 10) ──

    private final LinkedList<DedupEntry> dedupList = new LinkedList<>();
    private final HashSet<String> dedupSet = new HashSet<>();

    // ── Reconnect grace timers (host side, peerId -> Runnable) ──

    private final HashMap<String, Runnable> graceTimers = new HashMap<>();

    // ── Heartbeat ──

    private Runnable heartbeatRunnable;
    private byte[] lastBroadcastPacket; // stored for heartbeat re-broadcast
    private int lastBroadcastMessageId;

    // ── Migration/reconnect flags ──

    private boolean migrationInProgress = false;
    private boolean recoveryHostProbeActive = false;
    private Runnable recoveryHostProbeRunnable;
    private boolean reconnectInProgress = false;
    private boolean reconnectScanInProgress = false;
    private boolean reconnectJoinInProgress = false;
    private String reconnectSessionId;
    private String reconnectHostPeerId;
    private Runnable reconnectTimeoutRunnable;

    // ── Migration state (spec Section 8) ──

    private String migrationSuccessorId;
    private String migrationSessionId;
    private int migrationMaxClients;
    private String migrationRoomName;
    private int migrationEpoch;
    private boolean becomingHost;
    private Runnable migrationTimeoutRunnable;
    private String migrationOldHostId;
    private final HashSet<String> migrationExcludedSuccessors = new HashSet<>();

    // ── Inner data classes ──

    /** Room information decoded from advertisement */
    private static class RoomInfo {
        String roomId;
        String sessionId;
        String hostPeerId;
        char transport;
        int maxClients;
        int peerCount;
        String roomName;
        int rssi;
        long lastSeenMs;
        int protoVersion;
        boolean incompatible;
    }

    /** Session peer entry for roster tracking */
    private static class SessionPeer {
        String peerId;
        boolean isHost;
        String status; // "connected" or "reconnecting"
    }

    /** Fragment assembly tracking (spec Section 5.4) */
    private static class InboundAssembly {
        int count;
        int receivedCount;
        byte[][] slots;
        long updatedAt;

        InboundAssembly(int count) {
            this.count = count;
            this.receivedCount = 0;
            this.slots = new byte[count][];
            this.updatedAt = System.currentTimeMillis();
        }
    }

    /** Dedup entry (spec Section 10) */
    private static class DedupEntry {
        String key;
        long timestamp;
    }

    /** Parsed packet structure (spec Section 4.1) */
    private static class Packet {
        byte version;
        int messageId; // uint16
        String kind;
        String fromPeerId;
        String toPeerId;
        String msgType;
        byte[] payload;
    }

    // ══════════════════════════════════════════════════
    //  Constructor
    // ══════════════════════════════════════════════════

    @Keep
    public BleManager(Context context) {
        this.context = context;
        this.handler = new Handler(Looper.getMainLooper());
        this.bluetoothManager = (BluetoothManager) context.getSystemService(Context.BLUETOOTH_SERVICE);
        this.bluetoothAdapter = (bluetoothManager != null) ? bluetoothManager.getAdapter() : null;
        this.localPeerId = generateShortId();
        handler.post(this::requestBluetoothPermissions);
    }

    // ══════════════════════════════════════════════════
    //  Helpers
    // ══════════════════════════════════════════════════

    private boolean hasBluetoothPermissions() {
        if (Build.VERSION.SDK_INT >= 31) {
            return context.checkSelfPermission(Manifest.permission.BLUETOOTH_SCAN) == PackageManager.PERMISSION_GRANTED
                && context.checkSelfPermission(Manifest.permission.BLUETOOTH_CONNECT) == PackageManager.PERMISSION_GRANTED
                && context.checkSelfPermission(Manifest.permission.BLUETOOTH_ADVERTISE) == PackageManager.PERMISSION_GRANTED;
        }
        if (Build.VERSION.SDK_INT >= 23) {
            return context.checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED;
        }
        return true;
    }

    private static final int BLE_PERMISSION_REQUEST_CODE = 9001;

    private void requestBluetoothPermissions() {
        if (hasBluetoothPermissions()) return;
        if (!(context instanceof Activity)) return;
        Activity activity = (Activity) context;
        if (Build.VERSION.SDK_INT >= 31) {
            activity.requestPermissions(new String[]{
                Manifest.permission.BLUETOOTH_SCAN,
                Manifest.permission.BLUETOOTH_CONNECT,
                Manifest.permission.BLUETOOTH_ADVERTISE,
            }, BLE_PERMISSION_REQUEST_CODE);
        } else if (Build.VERSION.SDK_INT >= 23) {
            activity.requestPermissions(new String[]{
                Manifest.permission.ACCESS_FINE_LOCATION,
            }, BLE_PERMISSION_REQUEST_CODE);
        }
    }

    private static String generateShortId() {
        byte[] bytes = new byte[3];
        new java.security.SecureRandom().nextBytes(bytes);
        return String.format("%02x%02x%02x", bytes[0] & 0xFF, bytes[1] & 0xFF, bytes[2] & 0xFF);
    }

    /** Spec Section 3.2: NormalizeRoomName */
    private static String normalizeRoomName(String name) {
        if (name == null || name.isEmpty()) return "Room";
        String result = name.replace("|", " ").replace("\n", " ").replace("\r", " ");
        result = result.trim();
        if (result.isEmpty()) return "Room";
        if (result.length() > 8) result = result.substring(0, 8);
        return result;
    }

    /** Spec Section 3.1: Encode room advertisement string */
    private String encodeRoomAdvertisement() {
        return "LB" + (char)('0' + CURRENT_PROTOCOL_VERSION) + sessionId + localPeerId + transportChar
                + maxClients + peerCount + roomName;
    }

    /** Spec Section 3.4: Decode room from UTF-8 payload string */
    private static RoomInfo decodeRoomFromString(String str, String roomId, int rssi) {
        if (str == null || str.length() < 18) return null;
        if (!str.startsWith("LB")) return null;

        int protoVersion = str.charAt(2) - '0';

        RoomInfo room = new RoomInfo();
        room.roomId = roomId;
        room.protoVersion = protoVersion;
        room.incompatible = (protoVersion != CURRENT_PROTOCOL_VERSION);
        room.sessionId = str.substring(3, 9);
        room.hostPeerId = str.substring(9, 15);
        room.transport = str.charAt(15);
        room.maxClients = str.charAt(16) - '0';
        room.peerCount = str.charAt(17) - '0';
        room.roomName = (str.length() > 18) ? str.substring(18) : "";
        room.rssi = rssi;
        room.lastSeenMs = System.currentTimeMillis();

        if (room.transport != 'r' && room.transport != 's') return null;
        if (room.maxClients < 1 || room.maxClients > 7) return null;
        if (room.peerCount < 0 || room.peerCount > 9) return null;

        return room;
    }

    /** Spec Section 3.4: Decode room from scan result */
    private static RoomInfo decodeRoomFromScanResult(ScanResult result) {
        ScanRecord record = result.getScanRecord();
        if (record == null) return null;

        String roomId = result.getDevice().getAddress();
        int rssi = result.getRssi();

        // 1. Manufacturer data with company ID 0xFFFF
        byte[] mfrData = record.getManufacturerSpecificData(MANUFACTURER_COMPANY_ID);
        if (mfrData != null && mfrData.length > 0) {
            String payload = new String(mfrData, StandardCharsets.UTF_8);
            RoomInfo room = decodeRoomFromString(payload, roomId, rssi);
            if (room != null) return room;
        }

        // 2. Service data for our service UUID
        byte[] svcData = record.getServiceData(new ParcelUuid(SERVICE_UUID));
        if (svcData != null && svcData.length > 0) {
            String payload = new String(svcData, StandardCharsets.UTF_8);
            RoomInfo room = decodeRoomFromString(payload, roomId, rssi);
            if (room != null) return room;
        }

        // 3. Local name
        String localName = record.getDeviceName();
        if (localName != null) {
            RoomInfo room = decodeRoomFromString(localName, roomId, rssi);
            if (room != null) return room;
        }

        return null;
    }

    private void bleLog(String msg) {
        Log.d(TAG, msg);
        nativeOnDiagnostic(msg);
    }

    // ══════════════════════════════════════════════════
    //  Nonce and MessageID (spec Section 5.3 and 4.1)
    // ══════════════════════════════════════════════════

    /** Spec Section 5.3: NextNonce — wraps 65535->1, 0 is reserved */
    private int nextNonce() {
        nonceCounter++;
        if (nonceCounter > 0xFFFF) nonceCounter = 1;
        if (nonceCounter == 0) nonceCounter = 1;
        return nonceCounter;
    }

    /** NextMessageId — same 16-bit wrapping pattern as nonce */
    private int nextMessageId() {
        messageIdCounter++;
        if (messageIdCounter > 0xFFFF) messageIdCounter = 1;
        if (messageIdCounter == 0) messageIdCounter = 1;
        return messageIdCounter;
    }

    // ══════════════════════════════════════════════════
    //  Packet encoding (spec Section 4.1)
    // ══════════════════════════════════════════════════

    private static byte[] buildPacket(String kind, String fromPeerId, String toPeerId,
                                       String msgType, int messageId,
                                       byte[] payload) {
        byte[] kindBytes = kind.getBytes(StandardCharsets.UTF_8);
        byte[] fromBytes = fromPeerId.getBytes(StandardCharsets.UTF_8);
        byte[] toBytes = toPeerId.getBytes(StandardCharsets.UTF_8);
        byte[] typeBytes = msgType.getBytes(StandardCharsets.UTF_8);
        int payloadLen = (payload != null) ? payload.length : 0;

        int totalLen = 1 + 2 + 4 + kindBytes.length + 4 + fromBytes.length
                + 4 + toBytes.length + 4 + typeBytes.length + 4 + payloadLen;

        ByteBuffer buf = ByteBuffer.allocate(totalLen);
        buf.order(ByteOrder.BIG_ENDIAN);

        buf.put(PROTOCOL_VERSION);                      // Version
        buf.putShort((short) (messageId & 0xFFFF));     // MessageID
        buf.putInt(kindBytes.length);                    // KindLength
        buf.put(kindBytes);                              // Kind
        buf.putInt(fromBytes.length);                    // FromLength
        buf.put(fromBytes);                              // FromPeerID
        buf.putInt(toBytes.length);                      // ToLength
        buf.put(toBytes);                                // ToPeerID
        buf.putInt(typeBytes.length);                    // TypeLength
        buf.put(typeBytes);                              // MsgType
        buf.putInt(payloadLen);                          // PayloadLength
        if (payloadLen > 0) buf.put(payload);            // Payload

        return buf.array();
    }

    // ══════════════════════════════════════════════════
    //  Packet decoding (spec Section 4.1)
    // ══════════════════════════════════════════════════

    private static Packet decodePacket(byte[] data) {
        if (data == null || data.length < 1) return null;

        ByteBuffer buf = ByteBuffer.wrap(data);
        buf.order(ByteOrder.BIG_ENDIAN);

        // Version (1 byte)
        byte version = buf.get();
        if (version != PROTOCOL_VERSION) return null;

        // MessageID (2 bytes)
        if (buf.remaining() < 2) return null;
        int messageId = buf.getShort() & 0xFFFF;

        // Kind (length-prefixed string)
        if (buf.remaining() < 4) return null;
        int kindLen = buf.getInt();
        if (kindLen < 0 || kindLen > MAX_STRING_LENGTH || buf.remaining() < kindLen) return null;
        byte[] kindBytes = new byte[kindLen];
        buf.get(kindBytes);
        String kind = new String(kindBytes, StandardCharsets.UTF_8);

        // FromPeerID (length-prefixed string)
        if (buf.remaining() < 4) return null;
        int fromLen = buf.getInt();
        if (fromLen < 0 || fromLen > MAX_STRING_LENGTH || buf.remaining() < fromLen) return null;
        byte[] fromBytes = new byte[fromLen];
        buf.get(fromBytes);
        String fromPeerId = new String(fromBytes, StandardCharsets.UTF_8);

        // ToPeerID (length-prefixed string)
        if (buf.remaining() < 4) return null;
        int toLen = buf.getInt();
        if (toLen < 0 || toLen > MAX_STRING_LENGTH || buf.remaining() < toLen) return null;
        byte[] toBytes = new byte[toLen];
        buf.get(toBytes);
        String toPeerId = new String(toBytes, StandardCharsets.UTF_8);

        // MsgType (length-prefixed string)
        if (buf.remaining() < 4) return null;
        int typeLen = buf.getInt();
        if (typeLen < 0 || typeLen > MAX_STRING_LENGTH || buf.remaining() < typeLen) return null;
        byte[] typeBytes = new byte[typeLen];
        buf.get(typeBytes);
        String msgType = new String(typeBytes, StandardCharsets.UTF_8);

        // Payload (length-prefixed bytes)
        if (buf.remaining() < 4) return null;
        int payloadLen = buf.getInt();
        if (payloadLen < 0 || payloadLen > MAX_PAYLOAD_LENGTH || buf.remaining() < payloadLen) return null;
        byte[] payload = new byte[payloadLen];
        buf.get(payload);

        Packet pkt = new Packet();
        pkt.version = version;
        pkt.messageId = messageId;
        pkt.kind = kind;
        pkt.fromPeerId = fromPeerId;
        pkt.toPeerId = toPeerId;
        pkt.msgType = msgType;
        pkt.payload = payload;
        return pkt;
    }

    // ══════════════════════════════════════════════════
    //  Fragmentation (spec Section 5.2)
    // ══════════════════════════════════════════════════

    private List<byte[]> fragmentPacket(byte[] packetBytes, int payloadLimit) {
        int chunkSize = payloadLimit - FRAGMENT_HEADER_SIZE;
        if (chunkSize <= 0) {
            nativeOnError("send_failed", "");
            return null;
        }

        int packetLen = packetBytes.length;
        int fragmentCount = (packetLen + chunkSize - 1) / chunkSize;
        if (fragmentCount > 255) {
            nativeOnError("payload_too_large", "");
            return null;
        }

        int nonce = nextNonce();
        byte nonceHigh = (byte) ((nonce >> 8) & 0xFF);
        byte nonceLow = (byte) (nonce & 0xFF);

        List<byte[]> fragments = new ArrayList<>(fragmentCount);
        for (int i = 0; i < fragmentCount; i++) {
            int start = i * chunkSize;
            int end = Math.min(start + chunkSize, packetLen);
            int chunkLen = end - start;

            byte[] fragment = new byte[FRAGMENT_HEADER_SIZE + chunkLen];
            fragment[0] = PROTOCOL_VERSION;
            fragment[1] = nonceHigh;
            fragment[2] = nonceLow;
            fragment[3] = (byte) i;
            fragment[4] = (byte) fragmentCount;
            System.arraycopy(packetBytes, start, fragment, FRAGMENT_HEADER_SIZE, chunkLen);
            fragments.add(fragment);
        }
        return fragments;
    }

    // ══════════════════════════════════════════════════
    //  Fragment reassembly (spec Section 5.4)
    // ══════════════════════════════════════════════════

    private byte[] processIncomingFragment(String sourceKey, byte[] fragmentData) {
        // Step 1: < 5 bytes => reject silently
        if (fragmentData == null || fragmentData.length < FRAGMENT_HEADER_SIZE) return null;

        // Step 2: Parse header
        byte version = fragmentData[0];
        int nonce = ((fragmentData[1] & 0xFF) << 8) | (fragmentData[2] & 0xFF);
        int index = fragmentData[3] & 0xFF;
        int count = fragmentData[4] & 0xFF;

        // Step 3: version != 1 => reject silently
        if (version != PROTOCOL_VERSION) return null;

        // Step 4: count == 0 => reject silently
        if (count == 0) return null;

        // Step 5: index >= count => reject silently
        if (index >= count) return null;

        byte[] chunk = Arrays.copyOfRange(fragmentData, FRAGMENT_HEADER_SIZE, fragmentData.length);

        // Step 6: count == 1 => fast path, return payload immediately
        if (count == 1) return chunk;

        // Step 7: assemblyKey = sourceKey + ":" + nonce
        String assemblyKey = sourceKey + ":" + nonce;

        // Get or create source map
        HashMap<String, InboundAssembly> sourceMap = assemblerBySource.get(sourceKey);
        if (sourceMap == null) {
            sourceMap = new HashMap<>();
            assemblerBySource.put(sourceKey, sourceMap);
        }

        // Expire old assemblies (spec Section 5.5)
        expireAssemblies(sourceMap);

        // Step 8: Max concurrent assemblies per source
        if (sourceMap.size() >= MAX_CONCURRENT_ASSEMBLIES_PER_SOURCE && !sourceMap.containsKey(assemblyKey)) {
            // Discard oldest assembly
            String oldestKey = null;
            long oldestTime = Long.MAX_VALUE;
            for (Map.Entry<String, InboundAssembly> entry : sourceMap.entrySet()) {
                if (entry.getValue().updatedAt < oldestTime) {
                    oldestTime = entry.getValue().updatedAt;
                    oldestKey = entry.getKey();
                }
            }
            if (oldestKey != null) sourceMap.remove(oldestKey);
        }

        // Step 9: Look up or create assembly
        InboundAssembly assembly = sourceMap.get(assemblyKey);
        if (assembly == null) {
            // Step 10: Create new assembly
            assembly = new InboundAssembly(count);
            sourceMap.put(assemblyKey, assembly);
        } else {
            // Step 11: Existing assembly count mismatch => discard
            if (assembly.count != count) {
                sourceMap.remove(assemblyKey);
                return null;
            }
        }

        // Step 12: Check slot
        if (assembly.slots[index] != null) {
            if (Arrays.equals(assembly.slots[index], chunk)) {
                // 12a: benign duplicate, ignore
                return null;
            } else {
                // 12b: conflict, discard entire assembly
                sourceMap.remove(assemblyKey);
                return null;
            }
        }

        // Step 13: Store chunk
        assembly.slots[index] = chunk;
        assembly.receivedCount++;
        assembly.updatedAt = System.currentTimeMillis();

        // Step 14: Incomplete?
        if (assembly.receivedCount < assembly.count) return null;

        // Step 15: Concatenate all slots in index order
        int totalLen = 0;
        for (byte[] s : assembly.slots) totalLen += s.length;

        byte[] reassembled = new byte[totalLen];
        int offset = 0;
        for (byte[] s : assembly.slots) {
            System.arraycopy(s, 0, reassembled, offset, s.length);
            offset += s.length;
        }

        // Step 16: Remove assembly
        sourceMap.remove(assemblyKey);

        // Step 17: Check total length
        if (reassembled.length > MAX_PAYLOAD_LENGTH) {
            nativeOnError("payload_too_large", "");
            return null;
        }

        // Step 18: Return reassembled bytes
        return reassembled;
    }

    /** Spec Section 5.5: Expire assemblies older than 15 seconds */
    private void expireAssemblies(HashMap<String, InboundAssembly> sourceMap) {
        long now = System.currentTimeMillis();
        Iterator<Map.Entry<String, InboundAssembly>> it = sourceMap.entrySet().iterator();
        while (it.hasNext()) {
            if (now - it.next().getValue().updatedAt > ASSEMBLY_TIMEOUT_MS) {
                it.remove();
            }
        }
    }

    // ══════════════════════════════════════════════════
    //  Deduplication (spec Section 10)
    // ══════════════════════════════════════════════════

    /** IsDuplicate — applied only to "data" kind Packets */
    private boolean isDuplicate(String fromPeerId, String msgType, int messageId) {
        String key = fromPeerId + ":" + msgType + ":" + messageId;

        // Prune entries older than 5 seconds
        long now = System.currentTimeMillis();
        Iterator<DedupEntry> it = dedupList.iterator();
        while (it.hasNext()) {
            DedupEntry entry = it.next();
            if (now - entry.timestamp > DEDUP_EXPIRY_MS) {
                dedupSet.remove(entry.key);
                it.remove();
            }
        }

        // Prune if exceeding dedup window
        while (dedupList.size() > DEDUP_WINDOW) {
            DedupEntry oldest = dedupList.removeFirst();
            dedupSet.remove(oldest.key);
        }

        // Check if duplicate
        if (dedupSet.contains(key)) return true;

        // Add new entry
        DedupEntry entry = new DedupEntry();
        entry.key = key;
        entry.timestamp = now;
        dedupList.add(entry);
        dedupSet.add(key);

        return false;
    }

    private void clearDedupState() {
        dedupList.clear();
        dedupSet.clear();
    }

    // ══════════════════════════════════════════════════
    //  Session peers roster management
    // ══════════════════════════════════════════════════

    private void resetSessionPeers() {
        sessionPeers.clear();
    }

    private void addSessionPeer(String peerId, boolean isHost, String status) {
        // Avoid duplicates
        for (SessionPeer p : sessionPeers) {
            if (p.peerId.equals(peerId)) {
                p.status = status;
                p.isHost = isHost;
                return;
            }
        }
        SessionPeer peer = new SessionPeer();
        peer.peerId = peerId;
        peer.isHost = isHost;
        peer.status = status;
        sessionPeers.add(peer);
    }

    private void removeSessionPeer(String peerId) {
        Iterator<SessionPeer> it = sessionPeers.iterator();
        while (it.hasNext()) {
            if (it.next().peerId.equals(peerId)) {
                it.remove();
            }
        }
    }

    private boolean isKnownSessionPeer(String peerId) {
        for (SessionPeer p : sessionPeers) {
            if (p.peerId.equals(peerId)) return true;
        }
        return false;
    }

    private void updateSessionPeerStatus(String peerId, String status) {
        for (SessionPeer p : sessionPeers) {
            if (p.peerId.equals(peerId)) {
                p.status = status;
                return;
            }
        }
    }

    private boolean isSessionPeer(String peerId) {
        for (SessionPeer p : sessionPeers) {
            if (p.peerId.equals(peerId)) return true;
        }
        return false;
    }

    private String sessionPeerStatus(String peerId) {
        for (SessionPeer p : sessionPeers) {
            if (p.peerId.equals(peerId)) return p.status;
        }
        return null;
    }

    private int connectedClientCount() {
        return connectedClients.size();
    }

    // ══════════════════════════════════════════════════
    //  Roster snapshot encoding (spec Section 4.3)
    // ══════════════════════════════════════════════════

    /** Format: session_id|host_peer_id|membership_epoch|peer1:status|peer2:status|... */
    private byte[] encodeRosterSnapshotPayload() {
        StringBuilder sb = new StringBuilder();
        sb.append(sessionId != null ? sessionId : "");
        sb.append("|");
        sb.append(localPeerId);
        sb.append("|");
        sb.append(membershipEpoch);

        for (SessionPeer peer : sessionPeers) {
            sb.append("|");
            sb.append(peer.peerId);
            sb.append(":");
            sb.append(peer.status);
        }

        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }

    /** Compute roster fingerprint: CRC32 of sorted pipe-delimited peerID:status pairs */
    private int computeRosterFingerprint() {
        List<String> entries = new ArrayList<>();
        for (SessionPeer peer : sessionPeers) {
            String statusChar = "connected".equals(peer.status) ? "c" : "r";
            entries.add(peer.peerId + ":" + statusChar);
        }
        Collections.sort(entries);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < entries.size(); i++) {
            if (i > 0) sb.append("|");
            sb.append(entries.get(i));
        }

        CRC32 crc = new CRC32();
        crc.update(sb.toString().getBytes(StandardCharsets.UTF_8));
        return (int) crc.getValue();
    }

    /** Parse roster_snapshot payload and update local session peers */
    private void parseRosterSnapshot(String payloadStr) {
        String[] parts = payloadStr.split("\\|", -1);
        if (parts.length < 3) return;

        String snapSessionId = parts[0];
        String snapHostPeerId = parts[1];
        int snapEpoch;
        try {
            snapEpoch = Integer.parseInt(parts[2]);
        } catch (NumberFormatException e) {
            return;
        }

        // Update local state
        joinedSessionId = snapSessionId;
        hostPeerId = snapHostPeerId;
        membershipEpoch = snapEpoch;

        // Rebuild session peers from snapshot
        resetSessionPeers();
        addSessionPeer(snapHostPeerId, true, "connected");

        for (int i = 3; i < parts.length; i++) {
            String entry = parts[i];
            int colonIdx = entry.indexOf(':');
            if (colonIdx <= 0) continue;
            String peerId = entry.substring(0, colonIdx);
            String status = entry.substring(colonIdx + 1);
            addSessionPeer(peerId, false, status);
        }
    }

    // ══════════════════════════════════════════════════
    //  Host: send control packets
    // ══════════════════════════════════════════════════

    /** Send control packet to a specific device by address */
    private void sendControlToDevice(String deviceAddress, String msgType, String toPeerId, byte[] payload) {
        byte[] packetData = buildPacket("control", localPeerId, toPeerId, msgType, 0,
                payload != null ? payload : new byte[0]);

        int mtu = mtuForDevice(deviceAddress);
        int payloadLimit = mtu - ATT_OVERHEAD;
        List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
        if (fragments == null) return;

        enqueueNotifications(fragments, deviceAddress);
    }

    /** Send control packet to a specific peer by peerId */
    private void sendControlToPeer(String peerId, String msgType, byte[] payload) {
        String deviceAddress = deviceAddressForPeer(peerId);
        if (deviceAddress == null) return;
        sendControlToDevice(deviceAddress, msgType, peerId, payload);
    }

    /** Broadcast control to all connected clients */
    private void broadcastControl(String msgType, byte[] payload) {
        for (String peerId : new ArrayList<>(connectedClients.keySet())) {
            sendControlToPeer(peerId, msgType, payload);
        }
    }

    /** Broadcast control to all connected clients except one */
    private void broadcastControlExcept(String excludePeerId, String msgType, byte[] payload) {
        for (String peerId : new ArrayList<>(connectedClients.keySet())) {
            if (peerId.equals(excludePeerId)) continue;
            sendControlToPeer(peerId, msgType, payload);
        }
    }

    /** Look up device address for a peer ID */
    private String deviceAddressForPeer(String peerId) {
        for (Map.Entry<String, String> entry : devicePeerMap.entrySet()) {
            if (entry.getValue().equals(peerId)) return entry.getKey();
        }
        return null;
    }

    private int mtuForDevice(String deviceAddress) {
        Integer mtu = deviceMTUs.get(deviceAddress);
        return (mtu != null) ? mtu : DEFAULT_MTU;
    }

    // ══════════════════════════════════════════════════
    //  Host: notification queue (spec Section 15.2)
    // ══════════════════════════════════════════════════

    private void enqueueNotifications(List<byte[]> fragments, String deviceAddress) {
        LinkedList<byte[]> queue = notificationQueues.get(deviceAddress);
        if (queue == null) {
            queue = new LinkedList<>();
            notificationQueues.put(deviceAddress, queue);
        }
        queue.addAll(fragments);
        pumpNotificationQueue(deviceAddress);
    }

    private void pumpNotificationQueue(final String deviceAddress) {
        if (notificationInFlight.contains(deviceAddress)) return;

        LinkedList<byte[]> queue = notificationQueues.get(deviceAddress);
        if (queue == null || queue.isEmpty()) return;

        if (gattServer == null || messageCharacteristic == null) return;
        if (!subscribedCentrals.contains(deviceAddress)) return;

        BluetoothDevice device = bluetoothAdapter.getRemoteDevice(deviceAddress);
        if (device == null) return;

        byte[] fragment = queue.peek();
        messageCharacteristic.setValue(fragment);

        notificationInFlight.add(deviceAddress);
        boolean sent = gattServer.notifyCharacteristicChanged(device, messageCharacteristic, false);

        if (!sent) {
            notificationInFlight.remove(deviceAddress);
            // Will retry when onNotificationSent fires or we pump again
        }
    }

    // ══════════════════════════════════════════════════
    //  Client: write queue (spec Section 15.1)
    // ══════════════════════════════════════════════════

    private void enqueueClientWrites(List<byte[]> fragments) {
        clientWriteQueue.addAll(fragments);
        pumpClientWriteQueue();
    }

    private void pumpClientWriteQueue() {
        // Step 1: If a write is already in-flight, return
        if (writeInFlight) return;

        // Step 2-3: Peek first fragment
        if (clientWriteQueue.isEmpty()) return;

        if (clientGatt == null || remoteCharacteristic == null) return;

        byte[] fragment = clientWriteQueue.peek();

        // Step 4-5: Write fragment, set writeInFlight
        writeInFlight = true;
        remoteCharacteristic.setValue(fragment);
        remoteCharacteristic.setWriteType(BluetoothGattCharacteristic.WRITE_TYPE_DEFAULT);
        boolean result = clientGatt.writeCharacteristic(remoteCharacteristic);
        if (!result) {
            writeInFlight = false;
            clientWriteQueue.clear();
            departureWriteFragments.clear();
            nativeOnError("write_failed", "writeCharacteristic returned false");
            if (departureSendInProgress) {
                completeClientLeaveAfterDeparture();
            }
        }
    }

    // ══════════════════════════════════════════════════
    //  Client: send packets to host
    // ══════════════════════════════════════════════════

    private void clientSendPacket(byte[] packetData) {
        int payloadLimit = negotiatedMTU - ATT_OVERHEAD;
        List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
        if (fragments == null) return;
        enqueueClientWrites(fragments);
    }

    private void clientSendControl(String msgType, String toPeerId, byte[] payload) {
        byte[] packetData = buildPacket("control", localPeerId, toPeerId, msgType, 0,
                payload != null ? payload : new byte[0]);
        clientSendPacket(packetData);
    }

    private void completeClientLeaveAfterDeparture() {
        if (!departureSendInProgress) return;

        departureSendInProgress = false;
        departureWriteFragments.clear();

        if (departureSendTimeoutRunnable != null) {
            handler.removeCallbacks(departureSendTimeoutRunnable);
            departureSendTimeoutRunnable = null;
        }

        finishLeave();
    }

    private void sendClientLeavingAndLeave() {
        if (hostPeerId == null || hostPeerId.isEmpty()
                || clientGatt == null || remoteCharacteristic == null) {
            finishLeave();
            return;
        }

        byte[] packetData = buildPacket("control", localPeerId, hostPeerId, "client_leaving", 0, new byte[0]);
        int payloadLimit = negotiatedMTU - ATT_OVERHEAD;
        List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
        if (fragments == null || fragments.isEmpty()) {
            finishLeave();
            return;
        }

        clientLeaving = true;
        departureSendInProgress = true;
        departureWriteFragments.clear();
        departureWriteFragments.addAll(fragments);

        if (departureSendTimeoutRunnable != null) {
            handler.removeCallbacks(departureSendTimeoutRunnable);
        }
        departureSendTimeoutRunnable = () -> completeClientLeaveAfterDeparture();
        handler.postDelayed(departureSendTimeoutRunnable, DEPARTURE_SEND_TIMEOUT_MS);

        enqueueClientWrites(fragments);
    }

    private void clientSendData(String msgType, String toPeerId, byte[] payload) {
        int msgId = nextMessageId();
        byte[] packetData = buildPacket("data", localPeerId, toPeerId, msgType, msgId, payload);
        clientSendPacket(packetData);
    }

    // ══════════════════════════════════════════════════
    //  Host: send data packets
    // ══════════════════════════════════════════════════

    private void hostSendData(String msgType, String toPeerId, byte[] payload) {
        int msgId = nextMessageId();
        byte[] packetData = buildPacket("data", localPeerId, toPeerId, msgType, msgId, payload);

        if (toPeerId.isEmpty()) {
            // Store for heartbeat re-broadcast
            lastBroadcastPacket = packetData;
            lastBroadcastMessageId = msgId;

            // Broadcast to all connected clients
            for (String peerId : new ArrayList<>(connectedClients.keySet())) {
                String devAddr = deviceAddressForPeer(peerId);
                if (devAddr == null) continue;
                int mtu = mtuForDevice(devAddr);
                int payloadLimit = mtu - ATT_OVERHEAD;
                List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
                if (fragments != null) enqueueNotifications(fragments, devAddr);
            }
        } else {
            // Directed: find the device for this peer
            String devAddr = deviceAddressForPeer(toPeerId);
            if (devAddr == null) return;
            int mtu = mtuForDevice(devAddr);
            int payloadLimit = mtu - ATT_OVERHEAD;
            List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
            if (fragments != null) enqueueNotifications(fragments, devAddr);
        }
    }

    // ══════════════════════════════════════════════════
    //  Radio State
    // ══════════════════════════════════════════════════

    @Keep
    public String getRadioState() {
        if (bluetoothAdapter == null) return "unsupported";
        if (!hasBluetoothPermissions()) return "unauthorized";
        if (!bluetoothAdapter.isEnabled()) return "off";
        return "on";
    }

    // ══════════════════════════════════════════════════
    //  Hosting (spec Section 6.1)
    // ══════════════════════════════════════════════════

    @Keep
    public void host(String roomNameParam, int maxClientsParam, String transportParam) {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) {
            nativeOnDiagnostic("host: BLE not available");
            return;
        }
        if (!hasBluetoothPermissions()) {
            nativeOnError("unauthorized", "Bluetooth permissions not granted");
            return;
        }

        // Spec 6.1 step 2: Leave existing session
        leaveInternal();

        // Spec 6.1 step 3-6
        sessionId = generateShortId();
        roomName = normalizeRoomName(roomNameParam);
        maxClients = Math.max(1, Math.min(maxClientsParam, 7));
        transportChar = "resilient".equals(transportParam) ? 's' : 'r';
        peerCount = 0;
        membershipEpoch = 0;
        hosting = true;
        hostServiceReady = false;

        // Initialize host maps
        connectedClients.clear();
        devicePeerMap.clear();
        pendingClients.clear();
        notificationQueues.clear();
        notificationInFlight.clear();
        deviceMTUs.clear();
        subscribedCentrals.clear();
        cancelAllGraceTimers();

        // Initialize roster with self as host
        resetSessionPeers();
        addSessionPeer(localPeerId, true, "connected");

        // Spec 6.1 step 7-9: Open GATT Server
        gattServer = bluetoothManager.openGattServer(context, gattServerCallback);
        if (gattServer == null) {
            nativeOnDiagnostic("failed to open GATT server");
            hosting = false;
            return;
        }

        BluetoothGattCharacteristic characteristic = new BluetoothGattCharacteristic(
                CHARACTERISTIC_UUID,
                BluetoothGattCharacteristic.PROPERTY_READ
                        | BluetoothGattCharacteristic.PROPERTY_WRITE
                        | BluetoothGattCharacteristic.PROPERTY_NOTIFY,
                BluetoothGattCharacteristic.PERMISSION_READ
                        | BluetoothGattCharacteristic.PERMISSION_WRITE);

        BluetoothGattDescriptor cccd = new BluetoothGattDescriptor(
                CCCD_UUID,
                BluetoothGattDescriptor.PERMISSION_READ | BluetoothGattDescriptor.PERMISSION_WRITE);
        characteristic.addDescriptor(cccd);
        messageCharacteristic = characteristic;

        BluetoothGattService service = new BluetoothGattService(
                SERVICE_UUID, BluetoothGattService.SERVICE_TYPE_PRIMARY);
        service.addCharacteristic(characteristic);

        gattServer.addService(service);
    }

    // ── GATT Server Callback (host side) ──

    private final BluetoothGattServerCallback gattServerCallback = new BluetoothGattServerCallback() {
        @Override
        public void onServiceAdded(int status, BluetoothGattService service) {
            handler.post(() -> {
                if (status != BluetoothGatt.GATT_SUCCESS) {
                    nativeOnDiagnostic("addService failed: status=" + status);
                    if (migrationInProgress && becomingHost) {
                        failMigration();
                    }
                    return;
                }

                hostServiceReady = true;

                // Spec 6.1 step 10a: Advertise
                startAdvertising();

                // Start heartbeat
                startHeartbeat();

                // Check if this is a migration — complete migration instead of emitting hosted
                if (migrationInProgress && becomingHost) {
                    completeMigrationResume();
                } else {
                    // Spec 6.1 step 10c: Emit hosted event
                    String transport = (transportChar == 's') ? "resilient" : "reliable";
                    nativeOnHosted(sessionId, localPeerId, transport);
                }
            });
        }

        @Override
        public void onConnectionStateChange(BluetoothDevice device, int status, int newState) {
            handler.post(() -> {
                String deviceAddress = device.getAddress();

                if (newState == BluetoothProfile.STATE_CONNECTED) {
                    bleLog("device connected: " + deviceAddress);
                    // Add to pending clients with timestamp
                    pendingClients.put(deviceAddress, System.currentTimeMillis());
                } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                    bleLog("device disconnected: " + deviceAddress);
                    onHostClientDisconnected(deviceAddress);
                }
            });
        }

        @Override
        public void onCharacteristicReadRequest(BluetoothDevice device, int requestId,
                                                 int offset, BluetoothGattCharacteristic characteristic) {
            if (gattServer != null) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, 0, new byte[0]);
            }
        }

        @Override
        public void onCharacteristicWriteRequest(BluetoothDevice device, int requestId,
                                                  BluetoothGattCharacteristic characteristic,
                                                  boolean preparedWrite, boolean responseNeeded,
                                                  int offset, byte[] value) {
            if (responseNeeded && gattServer != null) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, 0, null);
            }

            // Post to handler for thread safety
            final String deviceAddress = device.getAddress();
            final byte[] data = (value != null) ? value.clone() : null;
            handler.post(() -> {
                if (data == null || !hosting) return;
                handleHostIncomingFragment(deviceAddress, data);
            });
        }

        @Override
        public void onDescriptorWriteRequest(BluetoothDevice device, int requestId,
                                              BluetoothGattDescriptor descriptor,
                                              boolean preparedWrite, boolean responseNeeded,
                                              int offset, byte[] value) {
            if (responseNeeded && gattServer != null) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, 0, null);
            }

            handler.post(() -> {
                String deviceAddress = device.getAddress();
                if (value != null && value.length == 2) {
                    if (value[0] == 0x01 && value[1] == 0x00) {
                        // Notifications enabled
                        subscribedCentrals.add(deviceAddress);
                        bleLog("CCCD subscribed: " + deviceAddress);
                    } else if (value[0] == 0x00 && value[1] == 0x00) {
                        // Notifications disabled
                        subscribedCentrals.remove(deviceAddress);
                        bleLog("CCCD unsubscribed: " + deviceAddress);
                    }
                }
            });
        }

        @Override
        public void onNotificationSent(BluetoothDevice device, int status) {
            handler.post(() -> {
                String deviceAddress = device.getAddress();
                notificationInFlight.remove(deviceAddress);

                LinkedList<byte[]> queue = notificationQueues.get(deviceAddress);
                if (queue != null && !queue.isEmpty()) {
                    queue.poll(); // Remove the sent fragment
                }

                if (status != BluetoothGatt.GATT_SUCCESS) {
                    // Clear queue on failure
                    if (queue != null) queue.clear();
                    return;
                }

                // Pump next fragment
                pumpNotificationQueue(deviceAddress);
            });
        }

        @Override
        public void onMtuChanged(BluetoothDevice device, int mtu) {
            handler.post(() -> {
                String deviceAddress = device.getAddress();
                deviceMTUs.put(deviceAddress, mtu);
                bleLog("host MTU changed: " + deviceAddress + " -> " + mtu);
            });
        }
    };

    // ── Host: incoming fragment handling ──

    private void handleHostIncomingFragment(String deviceAddress, byte[] fragmentData) {
        byte[] reassembled = processIncomingFragment(deviceAddress, fragmentData);
        if (reassembled == null) return;

        Packet packet = decodePacket(reassembled);
        if (packet == null) return;

        handleHostIncomingPacket(deviceAddress, packet);
    }

    // ══════════════════════════════════════════════════
    //  Host: incoming packet handling + routing (spec Section 4.4)
    // ══════════════════════════════════════════════════

    private void handleHostIncomingPacket(String deviceAddress, Packet packet) {
        // Handle control packets
        if ("control".equals(packet.kind)) {
            handleHostControlPacket(deviceAddress, packet);
            return;
        }

        // Handle data packets
        if ("data".equals(packet.kind)) {
            // Dedup check
            if (isDuplicate(packet.fromPeerId, packet.msgType, packet.messageId)) return;

            // Route per spec Section 4.4
            routeDataPacket(packet);
        }
    }

    /** Spec Section 4.4: Message routing rules (host relay behavior) */
    private void routeDataPacket(Packet packet) {
        String toPeerId = packet.toPeerId;

        if (toPeerId == null || toPeerId.isEmpty()) {
            // Broadcast: send to all connected clients except sender, deliver to host if not sender
            byte[] packetData = buildPacket(packet.kind, packet.fromPeerId, packet.toPeerId,
                    packet.msgType, packet.messageId, packet.payload);

            // Store for heartbeat
            lastBroadcastPacket = packetData;
            lastBroadcastMessageId = packet.messageId;

            for (String peerId : new ArrayList<>(connectedClients.keySet())) {
                if (peerId.equals(packet.fromPeerId)) continue;
                String devAddr = deviceAddressForPeer(peerId);
                if (devAddr == null) continue;
                int mtu = mtuForDevice(devAddr);
                int payloadLimit = mtu - ATT_OVERHEAD;
                List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
                if (fragments != null) enqueueNotifications(fragments, devAddr);
            }

            // Deliver to host if host is not the sender
            if (!localPeerId.equals(packet.fromPeerId)) {
                nativeOnMessage(packet.fromPeerId, packet.msgType, packet.payload);
            }
        } else if (toPeerId.equals(localPeerId)) {
            // Directed to host: deliver to host, do not relay
            nativeOnMessage(packet.fromPeerId, packet.msgType, packet.payload);
        } else if (connectedClients.containsKey(toPeerId)) {
            // Directed to a connected client: forward only to that client
            byte[] packetData = buildPacket(packet.kind, packet.fromPeerId, packet.toPeerId,
                    packet.msgType, packet.messageId, packet.payload);
            String devAddr = deviceAddressForPeer(toPeerId);
            if (devAddr != null) {
                int mtu = mtuForDevice(devAddr);
                int payloadLimit = mtu - ATT_OVERHEAD;
                List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
                if (fragments != null) enqueueNotifications(fragments, devAddr);
            }
        }
        // else: unknown or reconnecting peer => drop silently
    }

    /** Host: handle incoming control packet */
    private void handleHostControlPacket(String deviceAddress, Packet packet) {
        String msgType = packet.msgType;

        if ("hello".equals(msgType)) {
            onHelloReceived(deviceAddress, packet);
        } else if ("client_leaving".equals(msgType)) {
            onClientLeavingReceived(deviceAddress, packet);
        } else if ("roster_request".equals(msgType)) {
            // Respond with roster_snapshot
            String peerId = devicePeerMap.get(deviceAddress);
            if (peerId != null) {
                byte[] rosterPayload = encodeRosterSnapshotPayload();
                sendControlToPeer(peerId, "roster_snapshot", rosterPayload);
            }
        }
    }

    // ══════════════════════════════════════════════════
    //  Host: HELLO handshake (spec Section 6.5)
    // ══════════════════════════════════════════════════

    private void onHelloReceived(String deviceAddress, Packet packet) {
        // Step 1: Get peerId from packet
        String peerId = packet.fromPeerId;
        if (peerId == null || peerId.isEmpty()) {
            bleLog("hello: empty peerId, disconnecting");
            disconnectDevice(deviceAddress);
            return;
        }

        // Step 2: Parse payload — "session_id|join_intent|proto_version" (spec Section 4.3)
        // Missing proto_version field is treated as version 1 (spec Section 6.5)
        String payloadStr = new String(packet.payload, StandardCharsets.UTF_8);
        String[] helloParts = payloadStr.split("\\|", -1);
        String helloSessionId = helloParts.length > 0 ? helloParts[0] : "";
        String joinIntent = helloParts.length > 1 ? helloParts[1] : "fresh";
        int clientProtoVersion = 1;
        if (helloParts.length > 2 && !helloParts[2].isEmpty()) {
            try { clientProtoVersion = Integer.parseInt(helloParts[2]); }
            catch (NumberFormatException ignored) {}
        }

        // Step 3: Validate admission
        // 3a: room_full — if connected clients >= maxClients and peer not in grace
        boolean inGrace = graceTimers.containsKey(peerId);
        if (connectedClientCount() >= maxClients && !inGrace) {
            sendJoinRejected(deviceAddress, peerId, "room_full");
            return;
        }

        // 3b: duplicate_peer_id — already in connected clients
        if (connectedClients.containsKey(peerId)) {
            sendJoinRejected(deviceAddress, peerId, "duplicate_peer_id");
            return;
        }

        // 3c: stale_session — non-empty session ID doesn't match
        if (!helloSessionId.isEmpty() && !helloSessionId.equals(sessionId)) {
            sendJoinRejected(deviceAddress, peerId, "stale_session");
            return;
        }

        // 3d: wrong_target — ToPeerID doesn't match host
        if (packet.toPeerId != null && !packet.toPeerId.isEmpty()
                && !packet.toPeerId.equals(localPeerId)) {
            sendJoinRejected(deviceAddress, peerId, "wrong_target");
            return;
        }

        // 3e: migration_mismatch
        if ("migration_resume".equals(joinIntent) && !migrationInProgress) {
            sendJoinRejected(deviceAddress, peerId, "migration_mismatch");
            return;
        }

        // 3f: incompatible_version — protocol version mismatch (spec Section 6.5)
        if (clientProtoVersion != CURRENT_PROTOCOL_VERSION) {
            sendJoinRejected(deviceAddress, peerId, "incompatible_version");
            disconnectDevice(deviceAddress);
            return;
        }

        // Step 4: Remove from pending clients
        pendingClients.remove(deviceAddress);
        departureIntents.remove(peerId);

        // Step 5: Bind device -> peer
        devicePeerMap.put(deviceAddress, peerId);

        // Step 6: Bind peer -> device
        BluetoothDevice device = bluetoothAdapter.getRemoteDevice(deviceAddress);
        connectedClients.put(peerId, device);

        // Step 7: Send hello_ack
        sendControlToDevice(deviceAddress, "hello_ack", peerId, new byte[0]);

        // Step 8 or 9: Reconnect or new peer
        if (inGrace) {
            // Step 8: Reconnecting peer
            // 8a: Cancel grace timer
            Runnable graceRunnable = graceTimers.remove(peerId);
            if (graceRunnable != null) handler.removeCallbacks(graceRunnable);

            // 8b: Update status, increment epoch
            updateSessionPeerStatus(peerId, "connected");
            membershipEpoch++;

            // 8c: Emit peer_status
            nativeOnPeerStatus(peerId, "connected");

            // 8d: Broadcast roster_snapshot
            broadcastControl("roster_snapshot", encodeRosterSnapshotPayload());
        } else {
            // Step 9: New peer
            // 9a: Add to roster, increment epoch
            addSessionPeer(peerId, false, "connected");
            membershipEpoch++;

            // 9b: Emit peer_joined
            nativeOnPeerJoined(peerId);

            // 9c: Broadcast peer_joined to all OTHER clients
            byte[] emptyPayload = new byte[0];
            for (String otherPeerId : new ArrayList<>(connectedClients.keySet())) {
                if (otherPeerId.equals(peerId)) continue;
                byte[] pjPacket = buildPacket("control", peerId, otherPeerId,
                        "peer_joined", 0, emptyPayload);
                String devAddr = deviceAddressForPeer(otherPeerId);
                if (devAddr == null) continue;
                int mtu = mtuForDevice(devAddr);
                int payloadLimit = mtu - ATT_OVERHEAD;
                List<byte[]> fragments = fragmentPacket(pjPacket, payloadLimit);
                if (fragments != null) enqueueNotifications(fragments, devAddr);
            }

            // 9d: Broadcast roster_snapshot to all connected clients
            broadcastControl("roster_snapshot", encodeRosterSnapshotPayload());
        }

        // Step 10: Update advertisement (peer count changed)
        peerCount = connectedClientCount();
        restartAdvertising();
    }

    private void sendJoinRejected(String deviceAddress, String peerId, String reason) {
        byte[] reasonBytes = reason.getBytes(StandardCharsets.UTF_8);
        byte[] packetData = buildPacket("control", localPeerId, peerId, "join_rejected", 0, reasonBytes);

        int mtu = mtuForDevice(deviceAddress);
        int payloadLimit = mtu - ATT_OVERHEAD;
        List<byte[]> fragments = fragmentPacket(packetData, payloadLimit);
        if (fragments != null) {
            enqueueNotifications(fragments, deviceAddress);
        }

        // Disconnect after a short delay to let the rejection send
        handler.postDelayed(() -> disconnectDevice(deviceAddress), 200);
    }

    private void disconnectDevice(String deviceAddress) {
        if (gattServer != null) {
            BluetoothDevice device = bluetoothAdapter.getRemoteDevice(deviceAddress);
            if (device != null) {
                gattServer.cancelConnection(device);
            }
        }
    }

    // ══════════════════════════════════════════════════
    //  Host: client disconnect (spec Section 14)
    // ══════════════════════════════════════════════════

    private void onHostClientDisconnected(String deviceAddress) {
        // Step 1: Remove from pending, MTU, notification queues
        pendingClients.remove(deviceAddress);
        deviceMTUs.remove(deviceAddress);
        notificationQueues.remove(deviceAddress);
        notificationInFlight.remove(deviceAddress);
        subscribedCentrals.remove(deviceAddress);

        // Step 2: Look up peer ID
        String peerId = devicePeerMap.remove(deviceAddress);
        if (peerId == null) return;

        // Step 3a: Remove from connected clients
        connectedClients.remove(peerId);

        Long departureAt = departureIntents.remove(peerId);
        long now = System.currentTimeMillis();
        if (departureAt != null && now - departureAt <= DEPARTURE_INTENT_EXPIRY_MS) {
            removeSessionPeer(peerId);
            membershipEpoch++;

            nativeOnPeerLeft(peerId, "left");

            byte[] reasonBytes = "left".getBytes(StandardCharsets.UTF_8);
            for (String otherPeerId : new ArrayList<>(connectedClients.keySet())) {
                byte[] plPacket = buildPacket("control", peerId, otherPeerId,
                        "peer_left", 0, reasonBytes);
                String devAddr = deviceAddressForPeer(otherPeerId);
                if (devAddr == null) continue;
                int mtu = mtuForDevice(devAddr);
                int payloadLimit = mtu - ATT_OVERHEAD;
                List<byte[]> fragments = fragmentPacket(plPacket, payloadLimit);
                if (fragments != null) enqueueNotifications(fragments, devAddr);
            }

            broadcastControl("roster_snapshot", encodeRosterSnapshotPayload());
            peerCount = connectedClientCount();
            restartAdvertising();
            return;
        }

        // Step 3c: If hosting and not in migration departure
        if (hosting && !migrationInProgress) {
            beginPeerReconnectGrace(peerId);
        } else {
            removeSessionPeer(peerId);
            membershipEpoch++;
            peerCount = connectedClientCount();
            restartAdvertising();
        }
    }

    private void onClientLeavingReceived(String deviceAddress, Packet packet) {
        String peerId = packet.fromPeerId;
        if (peerId == null || peerId.isEmpty()) return;
        if (!connectedClients.containsKey(peerId)) return;

        departureIntents.put(peerId, System.currentTimeMillis());
    }

    // ══════════════════════════════════════════════════
    //  Host: reconnect grace (spec Section 7.2)
    // ══════════════════════════════════════════════════

    private void beginPeerReconnectGrace(final String peerId) {
        // Step 1-2: Already removed from connectedClients, but keep in roster

        // Step 3: Update status, increment epoch
        updateSessionPeerStatus(peerId, "reconnecting");
        membershipEpoch++;

        // Step 5: Emit peer_status
        nativeOnPeerStatus(peerId, "reconnecting");

        // Step 6: Broadcast roster_snapshot
        broadcastControl("roster_snapshot", encodeRosterSnapshotPayload());

        // Step 7: Schedule grace timeout (10 seconds)
        Runnable graceRunnable = () -> onGraceTimeout(peerId);
        graceTimers.put(peerId, graceRunnable);
        handler.postDelayed(graceRunnable, RECONNECT_TIMEOUT_MS);

        // Step 8: Update advertisement
        peerCount = connectedClientCount();
        restartAdvertising();
    }

    private void onGraceTimeout(String peerId) {
        graceTimers.remove(peerId);

        // Step 1: Remove from roster, increment epoch
        removeSessionPeer(peerId);
        membershipEpoch++;

        // Step 2: Emit peer_left
        nativeOnPeerLeft(peerId, "timeout");

        // Step 3: Broadcast peer_left to all remaining clients
        byte[] reasonBytes = "timeout".getBytes(StandardCharsets.UTF_8);
        for (String otherPeerId : new ArrayList<>(connectedClients.keySet())) {
            byte[] plPacket = buildPacket("control", peerId, otherPeerId,
                    "peer_left", 0, reasonBytes);
            String devAddr = deviceAddressForPeer(otherPeerId);
            if (devAddr == null) continue;
            int mtu = mtuForDevice(devAddr);
            int payloadLimit = mtu - ATT_OVERHEAD;
            List<byte[]> fragments = fragmentPacket(plPacket, payloadLimit);
            if (fragments != null) enqueueNotifications(fragments, devAddr);
        }

        // Step 4: Broadcast roster_snapshot
        broadcastControl("roster_snapshot", encodeRosterSnapshotPayload());

        // Step 5: Update advertisement
        peerCount = connectedClientCount();
        restartAdvertising();
    }

    private void cancelAllGraceTimers() {
        for (Runnable r : graceTimers.values()) {
            handler.removeCallbacks(r);
        }
        graceTimers.clear();
    }

    // ══════════════════════════════════════════════════
    //  Heartbeat (spec Section 9)
    // ══════════════════════════════════════════════════

    private void startHeartbeat() {
        stopHeartbeat();
        heartbeatRunnable = new Runnable() {
            @Override
            public void run() {
                if (!hosting) return;

                // Disconnect pending clients older than timeout
                long now = System.currentTimeMillis();
                Iterator<Map.Entry<String, Long>> it = pendingClients.entrySet().iterator();
                while (it.hasNext()) {
                    Map.Entry<String, Long> entry = it.next();
                    if (now - entry.getValue() > PENDING_CLIENT_TIMEOUT_MS) {
                        String addr = entry.getKey();
                        it.remove();
                        disconnectDevice(addr);
                    }
                }

                // Compute roster fingerprint and deliver to all connected clients
                int fingerprint = computeRosterFingerprint();
                byte[] fpBytes = new byte[4];
                fpBytes[0] = (byte) ((fingerprint >> 24) & 0xFF);
                fpBytes[1] = (byte) ((fingerprint >> 16) & 0xFF);
                fpBytes[2] = (byte) ((fingerprint >> 8) & 0xFF);
                fpBytes[3] = (byte) (fingerprint & 0xFF);

                // Send fingerprint as a control packet to all clients
                broadcastControl("heartbeat", fpBytes);

                // Re-broadcast last broadcast packet if any
                if (lastBroadcastPacket != null && !connectedClients.isEmpty()) {
                    for (String peerId : new ArrayList<>(connectedClients.keySet())) {
                        String devAddr = deviceAddressForPeer(peerId);
                        if (devAddr == null) continue;
                        int mtu = mtuForDevice(devAddr);
                        int payloadLimit = mtu - ATT_OVERHEAD;
                        // Use fresh fragment nonce via fragmentPacket
                        List<byte[]> fragments = fragmentPacket(lastBroadcastPacket, payloadLimit);
                        if (fragments != null) enqueueNotifications(fragments, devAddr);
                    }
                }

                handler.postDelayed(this, HEARTBEAT_INTERVAL_MS);
            }
        };
        handler.postDelayed(heartbeatRunnable, HEARTBEAT_INTERVAL_MS);
    }

    private void stopHeartbeat() {
        if (heartbeatRunnable != null) {
            handler.removeCallbacks(heartbeatRunnable);
            heartbeatRunnable = null;
        }
    }

    // ══════════════════════════════════════════════════
    //  Advertising
    // ══════════════════════════════════════════════════

    /** Spec Section 3.3: Advertise on Android */
    private void startAdvertising() {
        if (!hosting || !hostServiceReady) return;

        advertiser = bluetoothAdapter.getBluetoothLeAdvertiser();
        if (advertiser == null) {
            nativeOnDiagnostic("BLE advertiser not available");
            return;
        }

        byte[] payload = encodeRoomAdvertisement().getBytes(StandardCharsets.UTF_8);

        // Advertising data: service UUID
        AdvertiseData advertiseData = new AdvertiseData.Builder()
                .addServiceUuid(new ParcelUuid(SERVICE_UUID))
                .setIncludeDeviceName(false)
                .build();

        // Scan response: manufacturer specific data with company ID 0xFFFF
        AdvertiseData scanResponse = new AdvertiseData.Builder()
                .addManufacturerData(MANUFACTURER_COMPANY_ID, payload)
                .setIncludeDeviceName(false)
                .build();

        AdvertiseSettings settings = new AdvertiseSettings.Builder()
                .setAdvertiseMode(AdvertiseSettings.ADVERTISE_MODE_LOW_LATENCY)
                .setConnectable(true)
                .setTimeout(0)
                .build();

        advertiseCallback = new AdvertiseCallback() {
            @Override
            public void onStartSuccess(AdvertiseSettings settingsInEffect) {
                bleLog("advertising started");
            }

            @Override
            public void onStartFailure(int errorCode) {
                nativeOnDiagnostic("advertise failed: errorCode=" + errorCode);
            }
        };

        advertiser.startAdvertising(settings, advertiseData, scanResponse, advertiseCallback);
    }

    private void stopAdvertising() {
        if (advertiser != null && advertiseCallback != null) {
            advertiser.stopAdvertising(advertiseCallback);
            advertiseCallback = null;
        }
    }

    /** Stop and restart advertising with updated room info (e.g., peer count changed) */
    private void restartAdvertising() {
        stopAdvertising();
        startAdvertising();
    }

    // ══════════════════════════════════════════════════
    //  Scanning (spec Section 6.2)
    // ══════════════════════════════════════════════════

    @Keep
    public void scan() {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) {
            nativeOnDiagnostic("scan: BLE not available");
            return;
        }
        if (!hasBluetoothPermissions()) {
            nativeOnError("unauthorized", "Bluetooth permissions not granted");
            return;
        }

        // Spec 6.2 step 2-3
        stopScanInternal();
        discoveredRooms.clear();

        scanner = bluetoothAdapter.getBluetoothLeScanner();
        if (scanner == null) {
            nativeOnDiagnostic("BLE scanner not available");
            return;
        }

        // Spec 6.2 step 4: Low Latency, no service filter
        ScanSettings settings = new ScanSettings.Builder()
                .setScanMode(ScanSettings.SCAN_MODE_LOW_LATENCY)
                .setCallbackType(ScanSettings.CALLBACK_TYPE_ALL_MATCHES)
                .build();

        scanCallback = new ScanCallback() {
            @Override
            public void onScanResult(int callbackType, ScanResult result) {
                handler.post(() -> handleScanResult(result));
            }
        };

        scanning = true;
        scanner.startScan(null, settings, scanCallback);
        startRoomExpiryCheck();
    }

    private void handleScanResult(ScanResult result) {
        RoomInfo room = decodeRoomFromScanResult(result);
        if (room == null) return;

        discoveredRooms.put(room.roomId, room);

        // Recovery Host Probe (spec Section 8.2 step 7a) — check before other routing
        if (recoveryHostProbeActive) {
            onScanResultDuringRecoveryProbe(room);
            return;
        }

        // Check reconnect scan (reconnect takes priority check)
        if (reconnectScanInProgress && !migrationInProgress) {
            onScanResultDuringReconnect(room);
            return;
        }

        // Check migration scan: look for successor advertising our session
        if (migrationInProgress && !becomingHost) {
            onScanResultDuringMigration(room);
            return;
        }

        // Spec 6.2 step 5: emit room_found if not in migration or reconnect
        if (!migrationInProgress && !reconnectInProgress) {
            String transport = (room.transport == 's') ? "resilient" : "reliable";
            nativeOnRoomFound(room.roomId, room.sessionId, room.roomName,
                    transport, room.peerCount, room.maxClients, room.rssi,
                    room.protoVersion, room.incompatible);
        }
    }

    /** Handle scan result during Recovery Host Probe (spec Section 8.2 step 7a).
     *  Invoked only when recoveryHostProbeActive is true and we are the elected successor. */
    private void onScanResultDuringRecoveryProbe(RoomInfo room) {
        if (migrationSessionId == null) return;
        if (!room.sessionId.equals(migrationSessionId)) return;

        if (room.hostPeerId.equals(migrationOldHostId)) {
            // Old host is still alive — abort self-election, reconnect to it
            bleLog("recoveryHostProbe: old host still alive, reconnecting");
            cancelRecoveryHostProbe();
            clearMigrationState();
            beginClientReconnect();
        } else if (isKnownSessionPeer(room.hostPeerId)) {
            // Another session peer is already advertising as host — connect to them
            bleLog("recoveryHostProbe: peer " + room.hostPeerId + " already hosting, connecting");
            cancelRecoveryHostProbe();
            migrationSuccessorId = room.hostPeerId;
            hostPeerId = room.hostPeerId;
            becomingHost = false;
            stopScanInternal();
            connectToRoom(room, true);
        }
        // Otherwise: ignore — keep scanning until probe timer fires
    }

    private void cancelRecoveryHostProbe() {
        recoveryHostProbeActive = false;
        if (recoveryHostProbeRunnable != null) {
            handler.removeCallbacks(recoveryHostProbeRunnable);
            recoveryHostProbeRunnable = null;
        }
        stopScanInternal();
    }

    private void clearMigrationState() {
        migrationInProgress = false;
        becomingHost = false;
        migrationSuccessorId = null;
        migrationSessionId = null;
        migrationMaxClients = 0;
        migrationRoomName = null;
        migrationEpoch = 0;
        migrationOldHostId = null;
        migrationExcludedSuccessors.clear();
        cancelMigrationTimeout();
    }

    /** Handle scan result during active migration — look for successor's advertisement.
     *  Implements spec Section 8.4 steps 2-3, including "first advertiser wins" rule. */
    private void onScanResultDuringMigration(RoomInfo room) {
        if (migrationSessionId == null) return;
        if (!room.sessionId.equals(migrationSessionId)) return;

        if (migrationSuccessorId != null && room.hostPeerId.equals(migrationSuccessorId)) {
            // Step 2: elected successor is advertising — connect
            bleLog("migration: found successor " + migrationSuccessorId + " advertising");
            stopScanInternal();
            hostPeerId = migrationSuccessorId;
            connectToRoom(room, true);
        } else if (isKnownSessionPeer(room.hostPeerId)) {
            // Step 3: "first advertiser wins" — a different known session member got there first
            bleLog("migration: first-advertiser-wins, peer " + room.hostPeerId + " hosting instead");
            stopScanInternal();
            migrationSuccessorId = room.hostPeerId;
            hostPeerId = room.hostPeerId;
            connectToRoom(room, true);
        }
    }

    private void stopScanInternal() {
        if (scanning && scanner != null && scanCallback != null) {
            try {
                scanner.stopScan(scanCallback);
            } catch (Exception e) {
                // Ignore if scan was already stopped
            }
            scanCallback = null;
        }
        scanning = false;
        stopRoomExpiryCheck();
    }

    // ── Room Expiry (spec Section 3.5) ──

    private void startRoomExpiryCheck() {
        stopRoomExpiryCheck();
        roomExpiryRunnable = new Runnable() {
            @Override
            public void run() {
                checkRoomExpiry();
                if (scanning) {
                    handler.postDelayed(this, ROOM_EXPIRY_CHECK_MS);
                }
            }
        };
        handler.postDelayed(roomExpiryRunnable, ROOM_EXPIRY_CHECK_MS);
    }

    private void stopRoomExpiryCheck() {
        if (roomExpiryRunnable != null) {
            handler.removeCallbacks(roomExpiryRunnable);
            roomExpiryRunnable = null;
        }
    }

    private void checkRoomExpiry() {
        long now = System.currentTimeMillis();
        Iterator<Map.Entry<String, RoomInfo>> it = discoveredRooms.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<String, RoomInfo> entry = it.next();
            if (now - entry.getValue().lastSeenMs > ROOM_EXPIRY_MS) {
                nativeOnRoomLost(entry.getKey());
                it.remove();
            }
        }
    }

    // ══════════════════════════════════════════════════
    //  Joining a Room (spec Section 6.3)
    // ══════════════════════════════════════════════════

    @Keep
    public void join(String roomId) {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) {
            nativeOnDiagnostic("join: BLE not available");
            return;
        }
        if (!hasBluetoothPermissions()) {
            nativeOnError("unauthorized", "Bluetooth permissions not granted");
            return;
        }

        // Step 2: Look up room
        RoomInfo room = discoveredRooms.get(roomId);
        if (room == null) {
            nativeOnError("room_gone", "");
            return;
        }

        // Step 4: Connect
        connectToRoom(room, false);
    }

    /** ConnectToRoom (spec Section 6.3) */
    private void connectToRoom(RoomInfo room, boolean migrationJoin) {
        // Step 1: Duplicate join guard
        if (clientGatt != null && room.roomId.equals(joinedRoomId)
                && room.sessionId.equals(joinedSessionId)
                && room.hostPeerId.equals(hostPeerId)
                && !clientLeaving) {
            return;
        }

        // Step 2: Stop scan, clean up prior connection
        stopScanInternal();
        stopClientOnly();

        // Step 3: Store session info
        joinedRoomId = room.roomId;
        joinedSessionId = room.sessionId;
        hostPeerId = room.hostPeerId;
        transportChar = room.transport;
        maxClients = room.maxClients;

        // Step 4: Reset flags
        clientLeaving = false;
        clientJoined = false;

        // Step 5: Reset roster if fresh join
        if (!migrationJoin && !reconnectJoinInProgress) {
            resetSessionPeers();
        }

        // Step 6: Connect GATT with autoConnect=false
        BluetoothDevice device = bluetoothAdapter.getRemoteDevice(room.roomId);
        negotiatedMTU = DEFAULT_MTU;
        clientGatt = device.connectGatt(context, false, gattClientCallback);
    }

    /** StopClientOnly: clean up GATT client state without session teardown */
    private void stopClientOnly() {
        writeInFlight = false;
        clientWriteQueue.clear();
        departureWriteFragments.clear();
        departureSendInProgress = false;
        if (departureSendTimeoutRunnable != null) {
            handler.removeCallbacks(departureSendTimeoutRunnable);
            departureSendTimeoutRunnable = null;
        }

        if (clientGatt != null) {
            try {
                clientGatt.disconnect();
                clientGatt.close();
            } catch (Exception e) {
                // Ignore
            }
            clientGatt = null;
        }
        remoteCharacteristic = null;
        negotiatedMTU = DEFAULT_MTU;
    }

    private void handleClientConnectFailure(String detail) {
        stopClientOnly();

        if (reconnectJoinInProgress) {
            reconnectJoinInProgress = false;
            reconnectScanInProgress = true;
            scanForReconnect();
            return;
        }

        if (migrationInProgress && !becomingHost) {
            scanForMigration();
            return;
        }

        finishLeaveClient();
        nativeOnError("join_failed", detail);
    }

    // ── GATT Client Callback ──

    private final BluetoothGattCallback gattClientCallback = new BluetoothGattCallback() {
        @Override
        public void onConnectionStateChange(BluetoothGatt gatt, int status, int newState) {
            handler.post(() -> {
                if (gatt != clientGatt) {
                    return;
                }
                if (newState == BluetoothProfile.STATE_CONNECTED) {
                    bleLog("client GATT connected");
                    // Step 7a: Request MTU
                    gatt.requestMtu(DESIRED_MTU);
                } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                    bleLog("client GATT disconnected, status=" + status);
                    if (!clientJoined && status != BluetoothGatt.GATT_SUCCESS) {
                        handleClientConnectFailure("connection_failed (gatt_status=" + status + ")");
                        return;
                    }
                    onClientDisconnected(clientJoined, !clientLeaving);
                }
            });
        }

        @Override
        public void onMtuChanged(BluetoothGatt gatt, int mtu, int status) {
            handler.post(() -> {
                if (gatt != clientGatt) {
                    return;
                }
                if (status == BluetoothGatt.GATT_SUCCESS) {
                    negotiatedMTU = mtu;
                    bleLog("client MTU: " + mtu);
                } else {
                    negotiatedMTU = DEFAULT_MTU;
                    bleLog("client MTU request failed, using default");
                }
                // Step 7b: Discover services
                gatt.discoverServices();
            });
        }

        @Override
        public void onServicesDiscovered(BluetoothGatt gatt, int status) {
            handler.post(() -> {
                if (gatt != clientGatt) {
                    return;
                }
                if (status != BluetoothGatt.GATT_SUCCESS) {
                    bleLog("service discovery failed: " + status);
                    handleClientConnectFailure("service_discovery_failed (gatt_status=" + status + ")");
                    return;
                }

                // Step 7c: Find message characteristic
                BluetoothGattService service = gatt.getService(SERVICE_UUID);
                if (service == null) {
                    bleLog("service not found");
                    handleClientConnectFailure("service_not_found");
                    return;
                }

                remoteCharacteristic = service.getCharacteristic(CHARACTERISTIC_UUID);
                if (remoteCharacteristic == null) {
                    bleLog("characteristic not found");
                    handleClientConnectFailure("characteristic_not_found");
                    return;
                }

                // Step 7d: Enable notifications via CCCD descriptor write
                gatt.setCharacteristicNotification(remoteCharacteristic, true);
                BluetoothGattDescriptor cccd = remoteCharacteristic.getDescriptor(CCCD_UUID);
                if (cccd != null) {
                    cccd.setValue(BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE);
                    gatt.writeDescriptor(cccd);
                } else {
                    // No CCCD, proceed anyway
                    completeLocalJoin();
                }
            });
        }

        @Override
        public void onDescriptorWrite(BluetoothGatt gatt, BluetoothGattDescriptor descriptor, int status) {
            handler.post(() -> {
                if (gatt != clientGatt) {
                    return;
                }
                if (CCCD_UUID.equals(descriptor.getUuid())) {
                    if (status == BluetoothGatt.GATT_SUCCESS) {
                        bleLog("CCCD write success");
                    } else {
                        bleLog("CCCD write failed: " + status);
                    }
                    // Step 7e: CompleteLocalJoin
                    completeLocalJoin();
                }
            });
        }

        @Override
        public void onCharacteristicWrite(BluetoothGatt gatt, BluetoothGattCharacteristic characteristic, int status) {
            handler.post(() -> {
                if (gatt != clientGatt) {
                    return;
                }
                // Spec Section 15.1 step 6
                if (!clientWriteQueue.isEmpty()) {
                    byte[] writtenFragment = clientWriteQueue.peek();
                    if (!departureWriteFragments.isEmpty()
                            && writtenFragment == departureWriteFragments.peek()) {
                        departureWriteFragments.poll();
                    }
                    clientWriteQueue.poll(); // Remove written fragment
                }
                writeInFlight = false;

                if (status != BluetoothGatt.GATT_SUCCESS) {
                    // Step 6c: Clear queue, emit error
                    clientWriteQueue.clear();
                    departureWriteFragments.clear();
                    nativeOnError("write_failed", "GATT write status=" + status);
                    if (departureSendInProgress) {
                        completeClientLeaveAfterDeparture();
                    }
                } else {
                    // Step 6d: Pump next
                    pumpClientWriteQueue();
                    if (departureSendInProgress && departureWriteFragments.isEmpty()) {
                        completeClientLeaveAfterDeparture();
                    }
                }
            });
        }

        @Override
        public void onCharacteristicChanged(BluetoothGatt gatt, BluetoothGattCharacteristic characteristic) {
            final byte[] value = characteristic.getValue();
            handler.post(() -> {
                if (gatt != clientGatt) {
                    return;
                }
                if (value == null) return;
                handleClientIncomingFragment(value);
            });
        }
    };

    // ══════════════════════════════════════════════════
    //  Client: join completion (spec Section 6.4)
    // ══════════════════════════════════════════════════

    private void completeLocalJoin() {
        // Step 1: Add local and host to roster
        addSessionPeer(localPeerId, false, "connected");
        addSessionPeer(hostPeerId, true, "connected");

        // Step 2: Enter pending state — do NOT emit joined yet

        // Step 3: Determine joinIntent
        String joinIntent;
        if (reconnectJoinInProgress) {
            joinIntent = "reconnect";
        } else if (migrationInProgress) {
            joinIntent = "migration_resume";
        } else {
            joinIntent = "fresh";
        }

        // Step 4: Determine sessionId for hello
        String helloSessionId;
        if ("fresh".equals(joinIntent) && (joinedSessionId == null || joinedSessionId.isEmpty())) {
            helloSessionId = "";
        } else {
            helloSessionId = (joinedSessionId != null) ? joinedSessionId : "";
        }

        // Step 5: Send HELLO — payload: "session_id|join_intent|proto_version" (spec Section 4.3)
        String helloPayload = helloSessionId + "|" + joinIntent + "|" + CURRENT_PROTOCOL_VERSION;
        clientSendControl("hello", hostPeerId, helloPayload.getBytes(StandardCharsets.UTF_8));

        // Step 6: Await host response (handled in packet handler)
    }

    // ══════════════════════════════════════════════════
    //  Client: incoming fragment handling
    // ══════════════════════════════════════════════════

    private void handleClientIncomingFragment(byte[] fragmentData) {
        // Use host address as source key for assembly
        String sourceKey = (joinedRoomId != null) ? joinedRoomId : "host";
        byte[] reassembled = processIncomingFragment(sourceKey, fragmentData);
        if (reassembled == null) return;

        Packet packet = decodePacket(reassembled);
        if (packet == null) return;

        handleClientIncomingPacket(packet);
    }

    private void handleClientIncomingPacket(Packet packet) {
        if ("control".equals(packet.kind)) {
            handleClientControlPacket(packet);
            return;
        }

        if ("data".equals(packet.kind)) {
            // Dedup check
            if (isDuplicate(packet.fromPeerId, packet.msgType, packet.messageId)) return;

            // Deliver to application
            nativeOnMessage(packet.fromPeerId, packet.msgType, packet.payload);
        }
    }

    private void handleClientControlPacket(Packet packet) {
        String msgType = packet.msgType;

        if ("hello_ack".equals(msgType)) {
            onHelloAckReceived();
        } else if ("join_rejected".equals(msgType)) {
            String reason = new String(packet.payload, StandardCharsets.UTF_8);
            onJoinRejectedReceived(reason);
        } else if ("peer_joined".equals(msgType)) {
            // FromPeerID is the peer that joined
            String peerId = packet.fromPeerId;
            if (peerId != null && !peerId.isEmpty()) {
                addSessionPeer(peerId, false, "connected");
                nativeOnPeerJoined(peerId);
            }
        } else if ("peer_left".equals(msgType)) {
            String peerId = packet.fromPeerId;
            String reason = new String(packet.payload, StandardCharsets.UTF_8);
            if (peerId != null && !peerId.isEmpty()) {
                removeSessionPeer(peerId);
                nativeOnPeerLeft(peerId, reason);
            }
        } else if ("roster_snapshot".equals(msgType)) {
            String payloadStr = new String(packet.payload, StandardCharsets.UTF_8);
            parseRosterSnapshot(payloadStr);
        } else if ("session_ended".equals(msgType)) {
            String reason = new String(packet.payload, StandardCharsets.UTF_8);
            clientLeaving = true;
            stopClientOnly();
            nativeOnSessionEnded(reason);
        } else if ("session_migrating".equals(msgType)) {
            onSessionMigratingReceived(packet);
        } else if ("heartbeat".equals(msgType)) {
            // Client-side roster fingerprint check
            if (packet.payload != null && packet.payload.length == 4) {
                int remoteFingerprint = ((packet.payload[0] & 0xFF) << 24)
                        | ((packet.payload[1] & 0xFF) << 16)
                        | ((packet.payload[2] & 0xFF) << 8)
                        | (packet.payload[3] & 0xFF);
                int localFingerprint = computeRosterFingerprint();
                if (remoteFingerprint != localFingerprint) {
                    // Request roster update
                    clientSendControl("roster_request", hostPeerId, new byte[0]);
                }
            }
        }
    }

    // ══════════════════════════════════════════════════
    //  Client: hello_ack / join_rejected (spec Section 6.4)
    // ══════════════════════════════════════════════════

    /** OnHelloAckReceived (spec Section 6.4) */
    private void onHelloAckReceived() {
        clientJoined = true;

        if (reconnectJoinInProgress) {
            completeReconnectResume();
        } else if (migrationInProgress) {
            completeMigrationResume();
        } else {
            // Fresh join
            String transport = (transportChar == 's') ? "resilient" : "reliable";
            nativeOnJoined(joinedSessionId, joinedRoomId, localPeerId, hostPeerId, transport);
        }
    }

    /** OnJoinRejectedReceived (spec Section 6.4) */
    private void onJoinRejectedReceived(String reason) {
        clientLeaving = true;
        stopClientOnly();
        nativeOnJoinFailed(reason, joinedRoomId != null ? joinedRoomId : "");
    }

    // ══════════════════════════════════════════════════
    //  Client: disconnect decision tree (spec Section 13)
    // ══════════════════════════════════════════════════

    private void onClientDisconnected(boolean wasJoined, boolean shouldEmit) {
        // Step 1: Clean up GATT state
        stopClientOnly();

        // Step 2: Active migration (spec Section 13 step 4)
        if (migrationInProgress) {
            beginMigrationReconnect();
            return;
        }

        // Step 3: Attempt reconnect (spec Section 13 step 5) — try this BEFORE recovery
        if (shouldEmit && wasJoined) {
            if (beginClientReconnect()) return;
        }

        // Step 4: Resilient transport recovery (spec Section 13 step 6)
        if (shouldEmit && wasJoined && transportChar == 's') {
            if (beginUnexpectedHostRecovery()) return;
        }

        // Step 5: Emit session ended or error (spec Section 13 step 7)
        if (shouldEmit) {
            finishLeaveClient();
            if (wasJoined) {
                nativeOnSessionEnded("host_lost");
            } else {
                nativeOnError("join_failed", "connection lost before join");
            }
            return;
        }

        // Step 6: Silent cleanup (spec Section 13 step 8)
        finishLeaveClient();
    }

    // ══════════════════════════════════════════════════
    //  Client: reconnect (spec Section 7.1)
    // ══════════════════════════════════════════════════

    private boolean beginClientReconnect() {
        if (joinedSessionId == null || joinedSessionId.isEmpty()
                || hostPeerId == null || hostPeerId.isEmpty()) {
            return false;
        }

        // Step 2: Save reconnect fields
        reconnectSessionId = joinedSessionId;
        reconnectHostPeerId = hostPeerId;

        // Step 3: Emit peer_status reconnecting
        reconnectInProgress = true;
        nativeOnPeerStatus(localPeerId, "reconnecting");

        // Step 4: Schedule reconnect timeout
        reconnectTimeoutRunnable = () -> onReconnectTimeout();
        handler.postDelayed(reconnectTimeoutRunnable, RECONNECT_TIMEOUT_MS);

        // Step 5-6: Start scan
        reconnectScanInProgress = true;
        scanForReconnect();

        return true;
    }

    private void scanForReconnect() {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) return;

        scanner = bluetoothAdapter.getBluetoothLeScanner();
        if (scanner == null) return;

        ScanSettings settings = new ScanSettings.Builder()
                .setScanMode(ScanSettings.SCAN_MODE_LOW_LATENCY)
                .setCallbackType(ScanSettings.CALLBACK_TYPE_ALL_MATCHES)
                .build();

        scanCallback = new ScanCallback() {
            @Override
            public void onScanResult(int callbackType, ScanResult result) {
                handler.post(() -> handleScanResult(result));
            }
        };

        scanning = true;
        scanner.startScan(null, settings, scanCallback);
        startRoomExpiryCheck();
    }

    /** OnScanResultDuringReconnect (spec Section 7.1) */
    private void onScanResultDuringReconnect(RoomInfo room) {
        if (reconnectSessionId == null || reconnectHostPeerId == null) return;

        // Step 1: Match saved session/host
        if (room.sessionId.equals(reconnectSessionId) && room.hostPeerId.equals(reconnectHostPeerId)) {
            reconnectJoinInProgress = true;
            connectToRoom(room, false);
        }
        // Step 2: Same host, different session (host restarted)
        else if (room.hostPeerId.equals(reconnectHostPeerId) && !room.sessionId.equals(reconnectSessionId)) {
            failReconnect();
        }
        // Step 3: Else ignore
    }

    /** CompleteReconnectResume (spec Section 7.1) */
    private void completeReconnectResume() {
        // Step 1: Cancel timeout
        if (reconnectTimeoutRunnable != null) {
            handler.removeCallbacks(reconnectTimeoutRunnable);
            reconnectTimeoutRunnable = null;
        }

        // Step 2: Clear reconnect state
        reconnectInProgress = false;
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;
        reconnectSessionId = null;
        reconnectHostPeerId = null;

        // Step 3: Emit peer_status connected
        nativeOnPeerStatus(localPeerId, "connected");
    }

    /** FailReconnect (spec Section 7.1) */
    private void failReconnect() {
        // Step 1: Cancel timeout
        if (reconnectTimeoutRunnable != null) {
            handler.removeCallbacks(reconnectTimeoutRunnable);
            reconnectTimeoutRunnable = null;
        }

        // Step 2: Clear state
        reconnectInProgress = false;
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;
        reconnectSessionId = null;
        reconnectHostPeerId = null;

        // Step 3: Stop scan
        stopScanInternal();

        // Step 4-5: Leave and emit
        finishLeaveClient();
        nativeOnSessionEnded("host_lost");
    }

    private void onReconnectTimeout() {
        // Spec Section 7.1 OnReconnectTimeout:
        // For Resilient transport, clear reconnect scan state (preserve session/host/roster)
        // and attempt unexpected host recovery before giving up.
        if (transportChar == 's') {
            if (reconnectTimeoutRunnable != null) {
                handler.removeCallbacks(reconnectTimeoutRunnable);
                reconnectTimeoutRunnable = null;
            }
            reconnectScanInProgress = false;
            reconnectJoinInProgress = false;
            stopScanInternal();
            // reconnectInProgress, joinedSessionId, hostPeerId, sessionPeers preserved intentionally
            if (beginUnexpectedHostRecovery()) return;
        }
        failReconnect();
    }

    // ══════════════════════════════════════════════════
    //  Migration (spec Section 8)
    // ══════════════════════════════════════════════════

    /** Spec Section 8.3: SelectSuccessor — collect connected client peer IDs
     *  (excluding grace peers), sort lexicographically, return first or null. */
    private String selectSuccessor() {
        List<String> candidates = new ArrayList<>();
        for (String peerId : connectedClients.keySet()) {
            if (!graceTimers.containsKey(peerId)) {
                candidates.add(peerId);
            }
        }
        if (candidates.isEmpty()) return null;
        Collections.sort(candidates);
        return candidates.get(0);
    }

    /** Spec Section 8.3: SelectRecoverySuccessor — collect session peers with status
     *  "connected", exclude the given host ID, sort, return first or null. */
    private String selectRecoverySuccessor(String excludeHostId) {
        List<String> candidates = new ArrayList<>();
        for (SessionPeer peer : sessionPeers) {
            if ("connected".equals(peer.status)
                    && !peer.peerId.equals(excludeHostId)
                    && !graceTimers.containsKey(peer.peerId)
                    && !migrationExcludedSuccessors.contains(peer.peerId)) {
                candidates.add(peer.peerId);
            }
        }
        if (candidates.isEmpty()) return null;
        Collections.sort(candidates);
        return candidates.get(0);
    }

    /** Spec Section 8.1: BeginGracefulMigration — host-initiated migration.
     *  Returns true if migration was initiated, false if no successor available. */
    private boolean beginGracefulMigration() {
        // Step 1: Cancel all reconnect grace timers. Remove grace peers from roster.
        for (String gracePeerId : new ArrayList<>(graceTimers.keySet())) {
            removeSessionPeer(gracePeerId);
        }
        cancelAllGraceTimers();
        membershipEpoch++;

        // Step 2: Select successor
        String successor = selectSuccessor();

        // Step 3: If no successor, return false
        if (successor == null) return false;

        // Step 4: Encode migration payload: sessionId|successorPeerID|maxClients|roomName|membershipEpoch
        String migrationPayload = sessionId + "|" + successor + "|" + maxClients + "|" + roomName + "|" + membershipEpoch;
        byte[] payload = migrationPayload.getBytes(StandardCharsets.UTF_8);

        // Step 5: Send session_migrating control to all clients
        broadcastControl("session_migrating", payload);

        // Step 6: Stop accepting new data writes (flag migration in progress)
        migrationInProgress = true;

        // Step 7: Schedule departure timer (400ms)
        handler.postDelayed(() -> {
            leaveInternal();
        }, MIGRATION_DEPARTURE_DELAY_MS);

        bleLog("beginGracefulMigration: successor=" + successor);

        return true;
    }

    /** Spec Section 8.2: BeginUnexpectedHostRecovery — resilient transport only.
     *  Called when client loses connection to host unexpectedly. */
    private boolean beginUnexpectedHostRecovery() {
        // Step 1: If transport is not Resilient, return false
        if (transportChar != 's') return false;

        // Step 2: If no valid session info, return false
        if (joinedSessionId == null || joinedSessionId.isEmpty()
                || hostPeerId == null || hostPeerId.isEmpty()) {
            return false;
        }

        String oldHostId = hostPeerId;
        migrationOldHostId = oldHostId;

        // Step 3: Remove old Host from session peer roster
        removeSessionPeer(oldHostId);
        // Ensure self is in roster
        addSessionPeer(localPeerId, false, "connected");

        // Step 4: Remove any peers known to be in reconnect grace from candidate set
        // (graceTimers is host-side only, but we track reconnecting status in roster)
        migrationExcludedSuccessors.clear();
        for (SessionPeer peer : sessionPeers) {
            if ("reconnecting".equals(peer.status)) {
                migrationExcludedSuccessors.add(peer.peerId);
            }
        }

        // Step 5: Select recovery successor excluding old host
        String successor = selectRecoverySuccessor(oldHostId);

        // Step 6: If no successor, return false
        if (successor == null) return false;

        // Step 7: Create migration info
        migrationInProgress = true;
        becomingHost = successor.equals(localPeerId);
        migrationSuccessorId = successor;
        migrationSessionId = joinedSessionId;
        migrationMaxClients = maxClients;
        migrationRoomName = (roomName != null) ? roomName : "Room";
        migrationEpoch = membershipEpoch;

        bleLog("beginUnexpectedHostRecovery: successor=" + successor
                + " becomingHost=" + becomingHost);

        // Step 7a: Recovery Host Probe (spec Section 8.2) — only when we are the elected successor.
        // Scan for RECOVERY_HOST_PROBE_DURATION_MS to check if old host is still alive or
        // another peer has already started advertising before committing to host role.
        if (becomingHost) {
            recoveryHostProbeActive = true;
            startProbeOrMigrationScan();
            recoveryHostProbeRunnable = () -> {
                recoveryHostProbeActive = false;
                bleLog("recoveryHostProbe: timeout, proceeding to host");
                beginMigrationReconnect();
            };
            handler.postDelayed(recoveryHostProbeRunnable, RECOVERY_HOST_PROBE_DURATION_MS);
            return true;
        }

        // Step 8-9: Begin migration reconnect (non-host path)
        beginMigrationReconnect();

        return true;
    }

    /** Start a low-latency BLE scan for the Recovery Host Probe or migration reconnect. */
    private void startProbeOrMigrationScan() {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) return;
        scanner = bluetoothAdapter.getBluetoothLeScanner();
        if (scanner == null) return;
        ScanSettings settings = new ScanSettings.Builder()
                .setScanMode(ScanSettings.SCAN_MODE_LOW_LATENCY)
                .setCallbackType(ScanSettings.CALLBACK_TYPE_ALL_MATCHES)
                .build();
        scanCallback = new ScanCallback() {
            @Override
            public void onScanResult(int callbackType, ScanResult result) {
                handler.post(() -> handleScanResult(result));
            }
        };
        scanning = true;
        scanner.startScan(null, settings, scanCallback);
    }

    /** Spec Section 8.4: BeginMigrationReconnect — either start hosting
     *  or scan for the new host. */
    private void beginMigrationReconnect() {
        if (becomingHost) {
            // Start hosting with migrated session info
            bleLog("migration: becoming new host for session " + migrationSessionId);

            // Leave client state
            stopClientOnly();

            // Begin hosting with the migrated session's parameters
            hostWithMigrationInfo();
        } else {
            // Start scan to find new host's advertisement
            bleLog("migration: scanning for new host " + migrationSuccessorId);

            stopClientOnly();
            scanForMigration();
        }

        // Schedule migration timeout (3 seconds)
        scheduleMigrationTimeout();
    }

    /** Start hosting using migrated session info instead of generating fresh IDs */
    private void hostWithMigrationInfo() {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) {
            failMigration();
            return;
        }

        // Set up host state with migrated session info
        sessionId = migrationSessionId;
        roomName = migrationRoomName;
        maxClients = migrationMaxClients;
        transportChar = 's'; // Migration only for resilient
        membershipEpoch = migrationEpoch;
        hosting = true;
        hostServiceReady = false;

        // Initialize host maps
        connectedClients.clear();
        devicePeerMap.clear();
        pendingClients.clear();
        notificationQueues.clear();
        notificationInFlight.clear();
        deviceMTUs.clear();
        subscribedCentrals.clear();
        cancelAllGraceTimers();

        // Remove old host from roster (mirroring spec Section 8.2 step 3)
        if (migrationOldHostId != null) {
            removeSessionPeer(migrationOldHostId);
        }

        // Set self as new host
        addSessionPeer(localPeerId, true, "connected");
        peerCount = 0; // No connected clients yet

        // Open GATT Server
        gattServer = bluetoothManager.openGattServer(context, gattServerCallback);
        if (gattServer == null) {
            bleLog("migration: failed to open GATT server");
            failMigration();
            return;
        }

        BluetoothGattCharacteristic characteristic = new BluetoothGattCharacteristic(
                CHARACTERISTIC_UUID,
                BluetoothGattCharacteristic.PROPERTY_READ
                        | BluetoothGattCharacteristic.PROPERTY_WRITE
                        | BluetoothGattCharacteristic.PROPERTY_NOTIFY,
                BluetoothGattCharacteristic.PERMISSION_READ
                        | BluetoothGattCharacteristic.PERMISSION_WRITE);

        BluetoothGattDescriptor cccd = new BluetoothGattDescriptor(
                CCCD_UUID,
                BluetoothGattDescriptor.PERMISSION_READ | BluetoothGattDescriptor.PERMISSION_WRITE);
        characteristic.addDescriptor(cccd);
        messageCharacteristic = characteristic;

        BluetoothGattService service = new BluetoothGattService(
                SERVICE_UUID, BluetoothGattService.SERVICE_TYPE_PRIMARY);
        service.addCharacteristic(characteristic);

        gattServer.addService(service);
        // onServiceAdded callback will call startAdvertising() and startHeartbeat()
        // completeMigrationResume() will be called once the service is ready
    }

    /** Scan for the new host during migration */
    private void scanForMigration() {
        if (bluetoothAdapter == null || !bluetoothAdapter.isEnabled()) {
            failMigration();
            return;
        }

        scanner = bluetoothAdapter.getBluetoothLeScanner();
        if (scanner == null) {
            failMigration();
            return;
        }

        ScanSettings settings = new ScanSettings.Builder()
                .setScanMode(ScanSettings.SCAN_MODE_LOW_LATENCY)
                .setCallbackType(ScanSettings.CALLBACK_TYPE_ALL_MATCHES)
                .build();

        scanCallback = new ScanCallback() {
            @Override
            public void onScanResult(int callbackType, ScanResult result) {
                handler.post(() -> handleScanResult(result));
            }
        };

        scanning = true;
        scanner.startScan(null, settings, scanCallback);
        startRoomExpiryCheck();
    }

    /** Spec Section 8.5: CompleteMigrationResume */
    private void completeMigrationResume() {
        // Step 1: Cancel migration timeout
        cancelMigrationTimeout();

        String resumeSessionId = migrationSessionId;
        String resumeNewHostId = migrationSuccessorId;

        // Step 3: Set local membershipEpoch from migration epoch
        membershipEpoch = migrationEpoch;

        // Step 2: Clear migration state
        // For the new host, keep migrationInProgress true briefly so that
        // peers arriving with migration_resume intent are accepted. Clear
        // after the migration timeout window.
        if (hosting && becomingHost) {
            becomingHost = false;
            migrationSuccessorId = null;
            migrationSessionId = null;
            migrationMaxClients = 0;
            migrationRoomName = null;
            migrationEpoch = 0;
            migrationOldHostId = null;
            migrationExcludedSuccessors.clear();
            // Keep migrationInProgress = true for a short acceptance window
            handler.postDelayed(() -> {
                migrationInProgress = false;
            }, MIGRATION_TIMEOUT_MS);
        } else {
            clearMigrationState();
        }

        // Step 4: Emit session_resumed event
        nativeOnSessionResumed(
                resumeSessionId != null ? resumeSessionId : "",
                resumeNewHostId != null ? resumeNewHostId : "");

        bleLog("completeMigrationResume: session=" + resumeSessionId
                + " newHost=" + resumeNewHostId);
    }

    /** FailMigration: migration could not be completed */
    private void failMigration() {
        bleLog("failMigration");

        // Cancel timeout
        cancelMigrationTimeout();

        // Clear migration state
        clearMigrationState();

        // Leave
        leaveInternal();

        // Emit session_ended
        nativeOnSessionEnded("migration_failed");
    }

    /** Spec Section 8.4: OnSessionMigratingReceived — client receives migration notice */
    private void onSessionMigratingReceived(Packet packet) {
        // Parse migration payload: sessionId|successorPeerID|maxClients|roomName|membershipEpoch
        String payloadStr = new String(packet.payload, StandardCharsets.UTF_8);
        String[] parts = payloadStr.split("\\|", -1);
        if (parts.length < 5) {
            bleLog("onSessionMigratingReceived: invalid payload: " + payloadStr);
            return;
        }

        String mSessionId = parts[0];
        String mSuccessorId = parts[1];
        int mMaxClients;
        try {
            mMaxClients = Integer.parseInt(parts[2]);
        } catch (NumberFormatException e) {
            mMaxClients = maxClients;
        }
        String mRoomName = parts[3];
        int mEpoch;
        try {
            mEpoch = Integer.parseInt(parts[4]);
        } catch (NumberFormatException e) {
            mEpoch = membershipEpoch;
        }

        // Store migration info
        migrationInProgress = true;
        migrationSuccessorId = mSuccessorId;
        migrationSessionId = mSessionId;
        migrationMaxClients = mMaxClients;
        migrationRoomName = mRoomName;
        migrationEpoch = mEpoch;
        migrationOldHostId = hostPeerId;
        becomingHost = mSuccessorId.equals(localPeerId);
        migrationExcludedSuccessors.clear();

        bleLog("onSessionMigratingReceived: successor=" + mSuccessorId
                + " becomingHost=" + becomingHost);

        // Emit session_migrating event
        nativeOnSessionMigrating(
                hostPeerId != null ? hostPeerId : "",
                mSuccessorId);

        // Spec Section 8.4: Discard write queue, clear assemblies
        clientWriteQueue.clear();
        writeInFlight = false;
        assemblerBySource.clear();

        // Proceed with migration reconnect
        beginMigrationReconnect();
    }

    /** Schedule migration timeout (3 seconds) — on timeout call failMigration or
     *  attempt convergence fallback per spec Section 8.3 */
    private void scheduleMigrationTimeout() {
        cancelMigrationTimeout();
        migrationTimeoutRunnable = () -> onMigrationTimeout();
        handler.postDelayed(migrationTimeoutRunnable, MIGRATION_TIMEOUT_MS);
    }

    /** Cancel migration timeout */
    private void cancelMigrationTimeout() {
        if (migrationTimeoutRunnable != null) {
            handler.removeCallbacks(migrationTimeoutRunnable);
            migrationTimeoutRunnable = null;
        }
    }

    /** Spec Section 8.3 convergence fallback: if elected successor didn't advertise,
     *  re-elect excluding that peer. Repeat until someone advertises or candidates
     *  exhausted, then emit session_ended. */
    private void onMigrationTimeout() {
        migrationTimeoutRunnable = null;

        if (!migrationInProgress) return;

        // If we were becoming host but timed out, that's a hard failure
        if (becomingHost) {
            failMigration();
            return;
        }

        // Convergence fallback: exclude the failed successor and re-elect
        bleLog("migration timeout: excluding successor " + migrationSuccessorId);
        migrationExcludedSuccessors.add(migrationSuccessorId);

        // Remove old host from candidates if set
        String excludeHost = (migrationOldHostId != null) ? migrationOldHostId : "";

        String newSuccessor = selectRecoverySuccessor(excludeHost);
        if (newSuccessor == null) {
            // No more candidates — session is lost
            bleLog("migration: no more successor candidates, session lost");
            cancelMigrationTimeout();
            clearMigrationState();
            stopScanInternal();
            finishLeaveClient();
            nativeOnSessionEnded("migration_failed");
            return;
        }

        // Re-elect with new successor
        migrationSuccessorId = newSuccessor;
        becomingHost = newSuccessor.equals(localPeerId);

        bleLog("migration: re-elected successor=" + newSuccessor
                + " becomingHost=" + becomingHost);

        if (becomingHost) {
            stopScanInternal();
            hostWithMigrationInfo();
        }
        // else: keep scanning for the new successor

        // Reschedule timeout
        scheduleMigrationTimeout();
    }

    // ══════════════════════════════════════════════════
    //  Leave (spec Section 6.6)
    // ══════════════════════════════════════════════════

    @Keep
    public void leave() {
        // If hosting with resilient transport and connected clients exist,
        // attempt graceful migration first (spec Section 8.1)
        if (hosting && transportChar == 's' && !connectedClients.isEmpty()) {
            if (beginGracefulMigration()) {
                // Migration initiated — departure will be scheduled (400ms)
                return;
            }
        }

        if (!hosting && clientJoined) {
            sendClientLeavingAndLeave();
            return;
        }

        leaveInternal();
    }

    private void leaveInternal() {
        // If hosting, send session_ended to all clients
        if (hosting && !connectedClients.isEmpty()) {
            byte[] reason = "host_left".getBytes(StandardCharsets.UTF_8);
            broadcastControl("session_ended", reason);
        }

        finishLeave();
    }

    private void finishLeave() {
        // Cancel all timers
        stopHeartbeat();
        cancelAllGraceTimers();
        cancelMigrationTimeout();
        departureIntents.clear();
        departureSendInProgress = false;
        departureWriteFragments.clear();
        if (departureSendTimeoutRunnable != null) {
            handler.removeCallbacks(departureSendTimeoutRunnable);
            departureSendTimeoutRunnable = null;
        }
        if (reconnectTimeoutRunnable != null) {
            handler.removeCallbacks(reconnectTimeoutRunnable);
            reconnectTimeoutRunnable = null;
        }

        // Clear reconnect state
        reconnectInProgress = false;
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;
        reconnectSessionId = null;
        reconnectHostPeerId = null;

        // Clear migration state
        clearMigrationState();

        // Clear dedup
        clearDedupState();

        // Stop advertising and scanning
        stopScanInternal();
        stopAdvertising();

        // Set flags
        hosting = false;
        clientLeaving = true;

        // Close GATT server
        if (gattServer != null) {
            gattServer.clearServices();
            gattServer.close();
            gattServer = null;
        }

        // Close GATT client
        stopClientOnly();

        // Clear all maps
        connectedClients.clear();
        devicePeerMap.clear();
        pendingClients.clear();
        notificationQueues.clear();
        notificationInFlight.clear();
        deviceMTUs.clear();
        subscribedCentrals.clear();
        discoveredRooms.clear();
        assemblerBySource.clear();

        // Reset session state
        messageCharacteristic = null;
        hostServiceReady = false;
        sessionId = null;
        peerCount = 0;
        membershipEpoch = 0;
        lastBroadcastPacket = null;
        lastBroadcastMessageId = 0;
        clientJoined = false;
        joinedRoomId = null;
        joinedSessionId = null;
        hostPeerId = null;
    }

    /** Client-only cleanup without tearing down host state */
    private void finishLeaveClient() {
        stopClientOnly();
        clearDedupState();
        assemblerBySource.clear();
        clientJoined = false;
        clientLeaving = true;
    }

    // ══════════════════════════════════════════════════
    //  Public send methods (called from JNI)
    // ══════════════════════════════════════════════════

    @Keep
    public void broadcast(String msgType, byte[] payload) {
        handler.post(() -> {
            if (hosting) {
                // Host: build data packet and send to all clients, deliver to self
                hostSendData(msgType, "", payload);
            } else if (clientGatt != null && clientJoined) {
                // Client: send data to host (empty toPeerId = broadcast)
                clientSendData(msgType, "", payload);
            }
        });
    }

    @Keep
    public void send(String peerId, String msgType, byte[] payload) {
        handler.post(() -> {
            if (hosting) {
                if (peerId.equals(localPeerId)) {
                    // Sending to self — deliver locally
                    nativeOnMessage(localPeerId, msgType, payload);
                } else {
                    // Host: send directed data to specific peer
                    hostSendData(msgType, peerId, payload);
                }
            } else if (clientGatt != null && clientJoined) {
                // Client: send directed data via host
                clientSendData(msgType, peerId, payload);
            }
        });
    }

    // ══════════════════════════════════════════════════
    //  State queries (called from JNI)
    // ══════════════════════════════════════════════════

    @Keep
    public String getLocalId() {
        return localPeerId;
    }

    @Keep
    public boolean isHosting() {
        return hosting;
    }

    @Keep
    public String getAddress() {
        if (bluetoothAdapter != null) {
            try {
                return bluetoothAdapter.getAddress();
            } catch (SecurityException e) {
                return "";
            }
        }
        return "";
    }

    @Keep
    public String getSessionId() {
        return (sessionId != null) ? sessionId : (joinedSessionId != null ? joinedSessionId : "");
    }

    @Keep
    public String getHostPeerId() {
        if (hosting) return localPeerId;
        return (hostPeerId != null) ? hostPeerId : "";
    }

    @Keep
    public String getTransport() {
        return (transportChar == 's') ? "resilient" : "reliable";
    }

    /** Return peers as pipe-delimited string: peerId:isHost:status|peerId:isHost:status|... */
    @Keep
    public String getPeersString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < sessionPeers.size(); i++) {
            if (i > 0) sb.append("|");
            SessionPeer p = sessionPeers.get(i);
            sb.append(p.peerId).append(":")
              .append(p.isHost ? "1" : "0").append(":")
              .append(p.status);
        }
        return sb.toString();
    }

    // ══════════════════════════════════════════════════
    //  Native JNI callbacks (implemented in android/Ble.cpp)
    // ══════════════════════════════════════════════════

    private native void nativeOnHosted(String sessionId, String peerId, String transport);
    private native void nativeOnJoined(String sessionId, String roomId, String peerId, String hostId, String transport);
    private native void nativeOnJoinFailed(String reason, String roomId);
    private native void nativeOnRoomFound(String roomId, String sessionId, String name,
                                           String transport, int peerCount, int max, int rssi,
                                           int protoVersion, boolean incompatible);
    private native void nativeOnRoomLost(String roomId);
    private native void nativeOnPeerJoined(String peerId);
    private native void nativeOnPeerLeft(String peerId, String reason);
    private native void nativeOnPeerStatus(String peerId, String status);
    private native void nativeOnMessage(String peerId, String msgType, byte[] payload);
    private native void nativeOnSessionMigrating(String oldHostId, String newHostId);
    private native void nativeOnSessionResumed(String sessionId, String newHostId);
    private native void nativeOnSessionEnded(String reason);
    private native void nativeOnError(String code, String detail);
    private native void nativeOnDiagnostic(String message);
}

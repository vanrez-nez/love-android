package org.love2d.android.ble;

import android.Manifest;
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
import android.bluetooth.le.AdvertiseCallback;
import android.bluetooth.le.AdvertiseData;
import android.bluetooth.le.AdvertiseSettings;
import android.bluetooth.le.BluetoothLeAdvertiser;
import android.bluetooth.le.BluetoothLeScanner;
import android.bluetooth.le.ScanCallback;
import android.bluetooth.le.ScanRecord;
import android.bluetooth.le.ScanResult;
import android.bluetooth.le.ScanSettings;
import android.content.Context;
import android.content.pm.PackageManager;
import android.location.LocationManager;
import android.os.Build;
import android.os.Handler;
import android.os.Looper;
import android.os.ParcelUuid;
import android.provider.Settings;
import android.util.Log;

import androidx.core.app.ActivityCompat;

import org.love2d.android.GameActivity;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Locale;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.UUID;

public class BleManager {
    private static final String LOG_TAG = "love-ble";
    private static final UUID SERVICE_UUID = UUID.fromString("4bdf6b6d-6b77-4b3f-9f4a-5a2d1499d641");
    private static final UUID MESSAGE_UUID = UUID.fromString("9e153f71-c2d0-4ee1-8b8d-090421bea607");
    private static final UUID CLIENT_CONFIG_UUID = UUID.fromString("00002902-0000-1000-8000-00805f9b34fb");
    private static final int MANUFACTURER_DATA_ID = 0xFFFF;
    private static final String PACKET_KIND_DATA = "data";
    private static final String PACKET_KIND_CONTROL = "control";
    private static final String CONTROL_HELLO = "hello";
    private static final String CONTROL_HELLO_ACK = "hello_ack";
    private static final String CONTROL_JOIN_REJECTED = "join_rejected";
    private static final String CONTROL_PEER_JOINED = "peer_joined";
    private static final String CONTROL_PEER_LEFT = "peer_left";
    private static final String CONTROL_ROSTER_SNAPSHOT = "roster_snapshot";
    private static final String CONTROL_ROSTER_REQUEST = "roster_request";
    private static final String CONTROL_SESSION_MIGRATING = "session_migrating";
    private static final String CONTROL_SESSION_ENDED = "session_ended";
    private static final String CONTROL_HEARTBEAT = "heartbeat";
    private static final String ROOM_DISCOVERY_PREFIX = "LB1";
    private static final int SHORT_ID_LENGTH = 6;
    private static final int PACKET_VERSION = 1;
    private static final int FRAGMENT_VERSION = 1;
    private static final int DEFAULT_ATT_MTU = 23;
    private static final int DESIRED_ATT_MTU = 185;
    private static final int ATT_PAYLOAD_OVERHEAD = 3;
    private static final int FRAGMENT_HEADER_SIZE = 5;
    private static final int MAX_FRAGMENT_COUNT = 255;
    private static final int MAX_REASSEMBLED_PACKET_SIZE = 64 * 1024;
    private static final long ASSEMBLY_TIMEOUT_MS = 15000L;
    private static final int MAX_ASSEMBLIES_PER_SOURCE = 32;
    private static final long MIGRATION_TIMEOUT_MS = 3000L;
    private static final long PENDING_CLIENT_TIMEOUT_MS = 5000L;

    private final GameActivity activity;
    private final Handler handler = new Handler(Looper.getMainLooper());
    private final BluetoothManager bluetoothManager;
    private final BluetoothAdapter bluetoothAdapter;
    private final BluetoothLeAdvertiser advertiser;
    private final BluetoothLeScanner scanner;
    private final Map<String, RoomInfo> rooms = new HashMap<>();
    private final Map<String, BluetoothDevice> connectedClients = new HashMap<>();
    private final Map<String, BluetoothDevice> pendingClients = new HashMap<>();
    private final Map<String, Long> pendingClientTimestamps = new HashMap<>();
    private final Map<String, String> devicePeerIds = new HashMap<>();
    private final Map<String, Integer> deviceMtu = new HashMap<>();
    private final Map<String, ArrayDeque<byte[]>> notificationQueues = new HashMap<>();
    private final Map<String, InboundAssembly> inboundAssemblies = new HashMap<>();
    private final ArrayDeque<byte[]> clientWriteQueue = new ArrayDeque<>();
    private final HashSet<String> sessionPeerIds = new HashSet<>();
    private final HashMap<String, String> rosterStatus = new HashMap<>(); // peerId -> "connected" or "reconnecting"
    private int membershipEpoch = 0;
    private int clientLocalEpoch = 0;
    private long lastRosterRequestMs = 0;

    private BluetoothGattServer gattServer;
    private BluetoothGatt clientGatt;
    private BluetoothGattCharacteristic serverMessageCharacteristic;
    private BluetoothGattCharacteristic clientMessageCharacteristic;
    private String sessionId = "";
    private String roomName = "";
    private String transport = "reliable";
    private int maxClients = 4;
    private String localPeerId = "";
    private String joinedRoomId = "";
    private String joinedSessionId = "";
    private String joinedRoomName = "";
    private String hostPeerId = "";
    private int joinedMaxClients = 4;
    private boolean hosting = false;
    private boolean scanning = false;
    private boolean clientLeaving = false;
    private boolean clientJoined = false;
    private boolean hostAnnounced = false;
    private boolean hostServiceReady = false;
    private boolean clientWriteInFlight = false;
    private boolean clientPendingHelloAck = false;
    private int clientMtu = DEFAULT_ATT_MTU;
    private int nextMessageNonce = 1;
    private int nextMessageId = 1;
    private int scanResultCount = 0;
    private MigrationInfo migration;
    private Runnable migrationTimeout;
    private Runnable migrationDeparture;
    private Runnable scanWatchdogShort;
    private Runnable scanWatchdogLong;
    private boolean migrationJoinInProgress = false;
    private boolean migrationDepartureInProgress = false;

    // Reconnect state (client-side)
    private static final long DEFAULT_RECONNECT_TIMEOUT_MS = 10000L;
    private long reconnectTimeoutMs = DEFAULT_RECONNECT_TIMEOUT_MS;
    private boolean reconnectScanInProgress = false;
    private boolean reconnectJoinInProgress = false;
    private Runnable reconnectTimeout;
    private String reconnectSessionId = "";
    private String reconnectHostPeerId = "";

    // Reconnect grace (host-side)
    private final Map<String, Runnable> peerReconnectTimeouts = new HashMap<>();

    private double reliabilityHeartbeatInterval = 2.0;
    private int reliabilityFragmentSpacingMs = 15;
    private int reliabilityDedupWindow = 64;
    private Runnable heartbeatTask;
    private byte[] lastBroadcastPacket;
    private final ArrayList<DedupEntry> dedupEntries = new ArrayList<>();
    private final HashSet<String> dedupLookup = new HashSet<>();
    private static final long DEDUP_EXPIRY_MS = 5000;
    // Metrics counters
    private int metricMsgOut = 0;
    private int metricMsgIn = 0;
    private int metricCtrlOut = 0;
    private int metricCtrlIn = 0;
    private int metricHeartbeatTx = 0;
    private int metricHeartbeatRx = 0;
    private int metricDedupHit = 0;
    private int metricFragmentTx = 0;
    private int metricFragmentRx = 0;
    private int metricFragmentDrop = 0;
    private int metricAssemblyTimeout = 0;
    private int metricWriteFail = 0;
    private int metricReconnectAttempt = 0;
    private int metricReconnectSuccess = 0;
    private int metricReconnectFail = 0;
    private int metricGraceStart = 0;
    private int metricGraceExpire = 0;
    private int metricGraceResume = 0;
    private int metricRosterRequest = 0;
    private int metricJoinReject = 0;

    private static native void nativeOnRoomFound(String roomId, String sessionId, String name, String transport, int peerCount, int maxClients, int rssi);
    private static native void nativeOnRoomLost(String roomId);
    private static native void nativeOnHosted(String sessionId, String peerId, String transport);
    private static native void nativeOnJoined(String sessionId, String roomId, String peerId, String hostId, String transport);
    private static native void nativeOnJoinFailed(String reason, String roomId);
    private static native void nativeOnPeerJoined(String peerId);
    private static native void nativeOnPeerLeft(String peerId, String reason);
    private static native void nativeOnMessage(String peerId, String msgType, byte[] payload);
    private static native void nativeOnSessionMigrating(String oldHostId, String newHostId);
    private static native void nativeOnSessionResumed(String sessionId, String newHostId);
    private static native void nativeOnSessionEnded(String reason);
    private static native void nativeOnError(String code, String detail);
    private static native void nativeOnPeerStatus(String peerId, String status);
    private static native void nativeOnDiagnostic(String message);

    private void bleLog(String message) {
        Log.i(LOG_TAG, message);
        nativeOnDiagnostic(message);
    }

    private void addSessionPeer(String peerId) {
        String safePeerId = safe(peerId);
        if (!safePeerId.isEmpty()) {
            sessionPeerIds.add(safePeerId);
        }
    }

    private void removeSessionPeer(String peerId) {
        String safePeerId = safe(peerId);
        if (!safePeerId.isEmpty()) {
            sessionPeerIds.remove(safePeerId);
        }
    }

    private void resetSessionPeers(String hostId) {
        sessionPeerIds.clear();
        addSessionPeer(localPeerId);
        addSessionPeer(hostId);
    }

    private String hexPreview(byte[] data) {
        if (data == null || data.length == 0) {
            return "<empty>";
        }

        int count = Math.min(data.length, 24);
        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < count; i++) {
            if (i > 0) {
                builder.append(' ');
            }
            builder.append(String.format("%02X", data[i] & 0xFF));
        }

        if (data.length > count) {
            builder.append(" ...");
        }

        return builder.toString();
    }

    private String packetSummary(String kind, String fromPeerId, String toPeerId, String msgType, byte[] payload) {
        return "kind=" + safe(kind)
            + " from=" + safe(fromPeerId)
            + " to=" + safe(toPeerId)
            + " type=" + safe(msgType)
            + " payload_len=" + safePayload(payload).length
            + " payload_hex=" + hexPreview(payload);
    }

    private String packetSummary(Packet packet) {
        if (packet == null) {
            return "<null packet>";
        }

        return packetSummary(packet.kind, packet.fromPeerId, packet.toPeerId, packet.msgType, packet.payload);
    }

    private String roomSummary(RoomInfo room) {
        if (room == null) {
            return "<null room>";
        }

        return "room=" + safe(room.roomId)
            + " session=" + safe(room.sessionId)
            + " host=" + safe(room.hostPeerId)
            + " transport=" + safe(room.transport)
            + " peers=" + room.peerCount + "/" + room.maxClients
            + " rssi=" + room.rssi
            + " name=" + safe(room.name);
    }

    private static class RoomInfo {
        String roomId;
        String sessionId;
        String hostPeerId;
        String name;
        String transport;
        int peerCount;
        int maxClients;
        int rssi;
        BluetoothDevice device;
    }

    private static class Packet {
        String kind = "";
        String fromPeerId = "";
        String toPeerId = "";
        String msgType = "";
        byte[] payload = new byte[0];
        int messageId = 0;
    }

    private static class InboundAssembly {
        int fragmentCount;
        byte[][] fragments;
        int receivedCount;
        int totalBytes;
        long updatedAtMs;
    }

    private static class ReassembledPacket {
        final byte[] data;
        final int nonce;
        ReassembledPacket(byte[] data, int nonce) {
            this.data = data;
            this.nonce = nonce;
        }
    }

    private static class DedupEntry {
        final String id;
        final long timestampMs;
        DedupEntry(String id, long timestampMs) {
            this.id = id;
            this.timestampMs = timestampMs;
        }
    }

    private static class MigrationInfo {
        String oldHostId = "";
        String newHostId = "";
        String sessionId = "";
        String roomName = "";
        String transport = "reliable";
        int maxClients = 4;
        int membershipEpoch = 0;
        boolean becomingHost = false;
        HashSet<String> excludedSuccessors = new HashSet<>();
    }

    public BleManager(GameActivity activity) {
        this.activity = activity;
        bluetoothManager = (BluetoothManager) activity.getSystemService(Context.BLUETOOTH_SERVICE);
        bluetoothAdapter = bluetoothManager != null ? bluetoothManager.getAdapter() : null;
        advertiser = bluetoothAdapter != null ? bluetoothAdapter.getBluetoothLeAdvertiser() : null;
        scanner = bluetoothAdapter != null ? bluetoothAdapter.getBluetoothLeScanner() : null;
        localPeerId = generateShortId();
    }

    public boolean hasBluetoothLE() {
        return activity.getPackageManager().hasSystemFeature(PackageManager.FEATURE_BLUETOOTH_LE)
            && bluetoothAdapter != null;
    }

    public boolean hasBluetoothPermissions() {
        if (!hasBluetoothLE()) {
            return false;
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            return ActivityCompat.checkSelfPermission(activity, Manifest.permission.BLUETOOTH_SCAN) == PackageManager.PERMISSION_GRANTED
                && ActivityCompat.checkSelfPermission(activity, Manifest.permission.BLUETOOTH_CONNECT) == PackageManager.PERMISSION_GRANTED
                && ActivityCompat.checkSelfPermission(activity, Manifest.permission.BLUETOOTH_ADVERTISE) == PackageManager.PERMISSION_GRANTED
                && ActivityCompat.checkSelfPermission(activity, Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED;
        }

        return ActivityCompat.checkSelfPermission(activity, Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED;
    }

    public void requestBluetoothPermissions(int requestCode) {
        if (hasBluetoothPermissions()) {
            return;
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            ActivityCompat.requestPermissions(activity, new String[]{
                Manifest.permission.BLUETOOTH_SCAN,
                Manifest.permission.BLUETOOTH_CONNECT,
                Manifest.permission.BLUETOOTH_ADVERTISE,
                Manifest.permission.ACCESS_FINE_LOCATION,
            }, requestCode);
        } else {
            ActivityCompat.requestPermissions(activity, new String[]{
                Manifest.permission.ACCESS_FINE_LOCATION,
            }, requestCode);
        }
    }

    public String getRadioState() {
        if (!hasBluetoothLE()) {
            return "unsupported";
        }
        if (!hasBluetoothPermissions()) {
            return "unauthorized";
        }
        if (!bluetoothAdapter.isEnabled()) {
            return "off";
        }
        return "on";
    }

    public String getAdapterAddress() {
        try {
            String address = bluetoothAdapter != null ? safe(bluetoothAdapter.getAddress()) : "";
            if (!address.isEmpty() && !"02:00:00:00:00:00".equals(address)) {
                return address;
            }

            String androidId = Settings.Secure.getString(activity.getContentResolver(), Settings.Secure.ANDROID_ID);
            return safe(androidId);
        } catch (SecurityException e) {
            return "";
        }
    }

    public String debugState() {
        StringBuilder s = new StringBuilder();
        s.append("hosting=").append(hosting ? 1 : 0).append(" scanning=").append(scanning ? 1 : 0).append("\n");
        s.append("local_id=").append(safe(localPeerId)).append("\n");
        s.append("session=").append(safe(sessionId)).append(" transport=").append(safe(transport)).append("\n");
        s.append("clients=").append(connectedClients.size()).append(" pending=").append(pendingClients.size()).append("\n");
        for (String peerId : connectedClients.keySet()) {
            s.append("  client: ").append(peerId).append("\n");
        }
        s.append("host_announced=").append(hostAnnounced ? 1 : 0).append(" service_ready=").append(hostServiceReady ? 1 : 0).append("\n");
        s.append("client_joined=").append(clientJoined ? 1 : 0).append(" write_inflight=").append(clientWriteInFlight ? 1 : 0).append(" queue=").append(clientWriteQueue.size()).append("\n");
        s.append("notify_queues=").append(notificationQueues.size()).append("\n");
        for (Map.Entry<String, ArrayDeque<byte[]>> entry : notificationQueues.entrySet()) {
            s.append("  queue[").append(entry.getKey()).append("]=").append(entry.getValue().size()).append(" fragments\n");
        }
        s.append("heartbeat=").append(heartbeatTask != null ? "active" : "off");
        s.append(" last_broadcast=").append(lastBroadcastPacket != null ? lastBroadcastPacket.length : 0).append(" bytes\n");
        s.append("metrics msg_out=").append(metricMsgOut).append(" msg_in=").append(metricMsgIn).append(" ctrl_out=").append(metricCtrlOut).append(" ctrl_in=").append(metricCtrlIn).append("\n");
        s.append("metrics heartbeat_tx=").append(metricHeartbeatTx).append(" heartbeat_rx=").append(metricHeartbeatRx).append(" dedup_hit=").append(metricDedupHit).append("\n");
        s.append("metrics frag_tx=").append(metricFragmentTx).append(" frag_rx=").append(metricFragmentRx).append(" frag_drop=").append(metricFragmentDrop).append(" asm_timeout=").append(metricAssemblyTimeout).append("\n");
        s.append("metrics write_fail=").append(metricWriteFail).append(" reconn_try=").append(metricReconnectAttempt).append(" reconn_ok=").append(metricReconnectSuccess).append(" reconn_fail=").append(metricReconnectFail).append("\n");
        s.append("metrics grace_start=").append(metricGraceStart).append(" grace_expire=").append(metricGraceExpire).append(" grace_resume=").append(metricGraceResume).append("\n");
        s.append("metrics roster_req=").append(metricRosterRequest).append(" join_reject=").append(metricJoinReject).append("\n");
        return s.toString();
    }

    public void applyReliabilityConfig(double heartbeatInterval, int fragmentSpacingMs, int dedupWindow) {
        this.reliabilityHeartbeatInterval = heartbeatInterval;
        this.reliabilityFragmentSpacingMs = fragmentSpacingMs;
        this.reliabilityDedupWindow = dedupWindow;
        bleLog("reliability config heartbeat=" + heartbeatInterval + "s fragment_spacing=" + fragmentSpacingMs + "ms dedup=" + dedupWindow);
    }

    private void startHeartbeat() {
        stopHeartbeat();
        if (reliabilityHeartbeatInterval <= 0) return;
        long intervalMs = (long) (reliabilityHeartbeatInterval * 1000);
        heartbeatTask = new Runnable() {
            @Override
            public void run() {
                if (!hosting) return;

                // Disconnect stale pending clients
                long now = System.currentTimeMillis();
                ArrayList<String> stale = new ArrayList<>();
                for (Map.Entry<String, Long> entry : pendingClientTimestamps.entrySet()) {
                    if (now - entry.getValue() > PENDING_CLIENT_TIMEOUT_MS) {
                        stale.add(entry.getKey());
                    }
                }
                for (String deviceKey : stale) {
                    BluetoothDevice device = pendingClients.remove(deviceKey);
                    pendingClientTimestamps.remove(deviceKey);
                    if (device != null) {
                        bleLog("pending client timeout device=" + deviceKey);
                        disconnectDevice(device);
                    }
                }

                // Send roster fingerprint to all connected clients
                if (!connectedClients.isEmpty()) {
                    int fingerprint = computeRosterFingerprint();
                    byte[] fpBytes = new byte[4];
                    fpBytes[0] = (byte) ((fingerprint >> 24) & 0xFF);
                    fpBytes[1] = (byte) ((fingerprint >> 16) & 0xFF);
                    fpBytes[2] = (byte) ((fingerprint >> 8) & 0xFF);
                    fpBytes[3] = (byte) (fingerprint & 0xFF);
                    metricHeartbeatTx++;
                    metricCtrlOut++;
                    notifyClients(encodePacket(PACKET_KIND_CONTROL, localPeerId, "", CONTROL_HEARTBEAT, fpBytes, 0), null);
                }

                // Re-broadcast last data packet
                if (!connectedClients.isEmpty() && lastBroadcastPacket != null) {
                    bleLog("heartbeat re-broadcast");
                    notifyClients(lastBroadcastPacket, null);
                }

                handler.postDelayed(this, intervalMs);
            }
        };
        handler.postDelayed(heartbeatTask, intervalMs);
    }

    private void stopHeartbeat() {
        if (heartbeatTask != null) {
            handler.removeCallbacks(heartbeatTask);
            heartbeatTask = null;
        }
        lastBroadcastPacket = null;
    }

    private boolean isDuplicateMessage(String fromPeerId, String msgType, int messageId) {
        long now = System.currentTimeMillis();

        // Cleanup expired entries
        while (!dedupEntries.isEmpty() && now - dedupEntries.get(0).timestampMs > DEDUP_EXPIRY_MS) {
            DedupEntry removed = dedupEntries.remove(0);
            dedupLookup.remove(removed.id);
        }

        // Cap at dedupWindow
        while (dedupEntries.size() > reliabilityDedupWindow) {
            DedupEntry removed = dedupEntries.remove(0);
            dedupLookup.remove(removed.id);
        }

        String id = fromPeerId + ":" + msgType + ":" + messageId;
        if (dedupLookup.contains(id)) {
            metricDedupHit++;
            bleLog("dedup: dropped " + id);
            return true;
        }

        dedupEntries.add(new DedupEntry(id, now));
        dedupLookup.add(id);
        return false;
    }

    public boolean host(String room, int maxClients, String transport) {
        if (!isReady("host_failed")) {
            return false;
        }

        leave();
        return beginHostingSession(trimRoomName(room), Math.max(1, Math.min(7, maxClients)), "resilient".equals(transport) ? "resilient" : "reliable", generateSessionId());
    }

    private boolean beginHostingSession(String roomName, int maxClients, String transport, String sessionId) {
        bleLog("beginHostingSession room=" + safe(roomName)
            + " session=" + safe(sessionId)
            + " host=" + safe(localPeerId)
            + " transport=" + safe(transport)
            + " max=" + maxClients);
        this.roomName = roomName;
        this.maxClients = maxClients;
        this.transport = transport;
        this.sessionId = sessionId;
        this.hosting = true;
        this.joinedRoomId = "";
        this.joinedSessionId = this.sessionId;
        this.joinedRoomName = this.roomName;
        this.joinedMaxClients = this.maxClients;
        this.hostPeerId = this.localPeerId;
        this.clientLeaving = false;
        this.hostAnnounced = false;
        this.hostServiceReady = false;
        this.membershipEpoch = 0;
        this.rosterStatus.clear();
        resetSessionPeers(this.localPeerId);

        try {
            gattServer = bluetoothManager.openGattServer(activity, gattServerCallback);
        } catch (SecurityException e) {
            nativeOnError("host_failed", "Bluetooth permission was lost.");
            hosting = false;
            return false;
        }

        if (gattServer == null) {
            nativeOnError("host_failed", "Could not create Bluetooth GATT server.");
            hosting = false;
            return false;
        }

        BluetoothGattService service = new BluetoothGattService(SERVICE_UUID, BluetoothGattService.SERVICE_TYPE_PRIMARY);
        serverMessageCharacteristic = new BluetoothGattCharacteristic(
            MESSAGE_UUID,
            BluetoothGattCharacteristic.PROPERTY_NOTIFY | BluetoothGattCharacteristic.PROPERTY_WRITE | BluetoothGattCharacteristic.PROPERTY_READ,
            BluetoothGattCharacteristic.PERMISSION_READ | BluetoothGattCharacteristic.PERMISSION_WRITE
        );
        BluetoothGattDescriptor descriptor = new BluetoothGattDescriptor(
            CLIENT_CONFIG_UUID,
            BluetoothGattDescriptor.PERMISSION_READ | BluetoothGattDescriptor.PERMISSION_WRITE
        );
        serverMessageCharacteristic.addDescriptor(descriptor);
        service.addCharacteristic(serverMessageCharacteristic);
        if (!gattServer.addService(service)) {
            nativeOnError("host_failed", "Could not register Bluetooth GATT service.");
            leaveHostOnly();
            hosting = false;
            return false;
        }

        startHeartbeat();
        return true;
    }

    public boolean scan() {
        bleLog("scan");
        if (!isReady("scan_failed")) {
            return false;
        }

        if (scanner == null) {
            nativeOnError("scan_failed", "Bluetooth scanner is unavailable.");
            return false;
        }

        stopScanInternal();
        rooms.clear();

        ScanSettings settings = new ScanSettings.Builder()
            .setScanMode(ScanSettings.SCAN_MODE_LOW_LATENCY)
            .build();

        try {
            // iOS room advertisements may omit the 128-bit service UUID when the
            // encoded room local name consumes the limited advertising budget.
            // Scan broadly and rely on decodeRoom to reject unrelated devices.
            scanner.startScan(null, settings, scanCallback);
            bleLog("scan started mode=low_latency filter=none");
            scanResultCount = 0;
            scanning = true;
            scheduleScanDiagnostics();
            return true;
        } catch (SecurityException e) {
            nativeOnError("scan_failed", "Bluetooth permission was lost.");
            return false;
        }
    }

    public boolean join(String roomId) {
        bleLog("join room=" + safe(roomId));
        if (!isReady("join_failed")) {
            return false;
        }

        RoomInfo room = rooms.get(roomId);
        if (room == null || room.device == null) {
            nativeOnError("room_gone", "Selected room is no longer available.");
            return false;
        }

        return connectToRoom(roomId, room, false);
    }

    private boolean connectToRoom(String roomId, RoomInfo room, boolean migrationJoin) {
        bleLog("connectToRoom migration=" + migrationJoin + " " + roomSummary(room));

        if (clientGatt != null
            && safe(joinedRoomId).equals(safe(roomId))
            && safe(joinedSessionId).equals(safe(room.sessionId))
            && safe(hostPeerId).equals(safe(room.hostPeerId))
            && !clientLeaving) {
            bleLog("connectToRoom ignored duplicate join room=" + safe(roomId)
                + " session=" + safe(room.sessionId)
                + " host=" + safe(room.hostPeerId));
            return true;
        }

        stopScanInternal();
        leaveClientOnly();

        joinedRoomId = roomId;
        joinedSessionId = room.sessionId;
        joinedRoomName = trimRoomName(room.name);
        joinedMaxClients = room.maxClients;
        hostPeerId = room.hostPeerId;
        transport = room.transport;
        clientLeaving = false;
        clientJoined = false;
        migrationJoinInProgress = migrationJoin;
        if (!migrationJoin && !reconnectJoinInProgress) {
            resetSessionPeers(room.hostPeerId);
        }

        try {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                clientGatt = room.device.connectGatt(activity, false, clientGattCallback, BluetoothDevice.TRANSPORT_LE);
            } else {
                clientGatt = room.device.connectGatt(activity, false, clientGattCallback);
            }
        } catch (SecurityException e) {
            nativeOnError("join_failed", "Bluetooth permission was lost.");
            clientGatt = null;
        }

        if (clientGatt == null) {
            if (migrationJoinInProgress) {
                failMigration();
            } else {
                nativeOnError("join_failed", "Could not create Bluetooth GATT client.");
            }
        }

        return clientGatt != null;
    }

    public void leave() {
        if (hosting && "resilient".equals(transport) && !connectedClients.isEmpty() && beginGracefulMigration()) {
            return;
        }

        finishLeave("host_left");
    }

    private void finishLeave(String remoteReason) {
        cancelMigrationTimeout();
        cancelPendingMigrationDeparture();
        cancelReconnectTimeout();
        cancelAllPeerReconnectGraces();
        reconnectSessionId = "";
        reconnectHostPeerId = "";
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;
        stopHeartbeat();
        dedupEntries.clear();
        dedupLookup.clear();
        metricMsgOut = 0; metricMsgIn = 0; metricCtrlOut = 0; metricCtrlIn = 0;
        metricHeartbeatTx = 0; metricHeartbeatRx = 0; metricDedupHit = 0;
        metricFragmentTx = 0; metricFragmentRx = 0; metricFragmentDrop = 0; metricAssemblyTimeout = 0;
        metricWriteFail = 0; metricReconnectAttempt = 0; metricReconnectSuccess = 0; metricReconnectFail = 0;
        metricGraceStart = 0; metricGraceExpire = 0; metricGraceResume = 0;
        metricRosterRequest = 0; metricJoinReject = 0;

        if (remoteReason != null) {
            notifyClientsSessionEnded(remoteReason);
        }

        stopAdvertisingInternal();
        stopScanInternal();
        hosting = false;
        clientLeaving = true;
        leaveHostOnly();
        leaveClientOnly();
        rooms.clear();
        joinedRoomId = "";
        joinedSessionId = "";
        joinedRoomName = "";
        hostPeerId = "";
        joinedMaxClients = 4;
        clientJoined = false;
        clientPendingHelloAck = false;
        hostAnnounced = false;
        hostServiceReady = false;
        migration = null;
        migrationJoinInProgress = false;
        migrationDepartureInProgress = false;
        membershipEpoch = 0;
        rosterStatus.clear();
        clientLocalEpoch = 0;
        lastRosterRequestMs = 0;
        pendingClientTimestamps.clear();
        sessionPeerIds.clear();
    }

    private boolean beginGracefulMigration() {
        // Cancel all reconnect grace; treat grace peers as departed
        for (String gracePeerId : new ArrayList<>(peerReconnectTimeouts.keySet())) {
            cancelPeerReconnectGrace(gracePeerId);
            removeSessionPeer(gracePeerId);
            rosterStatus.remove(gracePeerId);
        }
        if (!peerReconnectTimeouts.isEmpty()) {
            membershipEpoch++;
        }

        String successor = selectMigrationSuccessor();
        if (successor.isEmpty()) {
            return false;
        }

        MigrationInfo info = new MigrationInfo();
        info.oldHostId = localPeerId;
        info.newHostId = successor;
        info.sessionId = sessionId;
        info.roomName = roomName;
        info.transport = transport;
        info.maxClients = maxClients;

        byte[] payload = encodeMigrationPayload(info);
        if (payload == null) {
            finishLeave("migration_failed");
            return true;
        }

        metricCtrlOut++;
        if (!notifyClients(encodePacket(PACKET_KIND_CONTROL, localPeerId, "", CONTROL_SESSION_MIGRATING, payload, 0), null)) {
            finishLeave("migration_failed");
            return true;
        }

        migrationDepartureInProgress = true;
        cancelPendingMigrationDeparture();
        migrationDeparture = new Runnable() {
            @Override
            public void run() {
                migrationDeparture = null;
                finishLeave(null);
            }
        };
        handler.postDelayed(migrationDeparture, 400L);
        return true;
    }

    private String selectMigrationSuccessor() {
        if (connectedClients.isEmpty()) {
            return "";
        }

        // Exclude peers in reconnect grace
        ArrayList<String> peerIds = new ArrayList<>();
        for (String peerId : connectedClients.keySet()) {
            if (!isPeerInReconnectGrace(peerId)) {
                peerIds.add(peerId);
            }
        }
        Collections.sort(peerIds);
        return peerIds.isEmpty() ? "" : peerIds.get(0);
    }

    private String selectRecoverySuccessor(String oldHostId) {
        return selectRecoverySuccessorExcluding(oldHostId, new HashSet<>());
    }

    private String selectRecoverySuccessorExcluding(String oldHostId, HashSet<String> excluded) {
        ArrayList<String> peerIds = new ArrayList<>();
        for (String peerId : sessionPeerIds) {
            if (!safe(peerId).isEmpty()
                && !safe(peerId).equals(safe(oldHostId))
                && !isPeerInReconnectGrace(peerId)
                && !excluded.contains(peerId)) {
                peerIds.add(peerId);
            }
        }

        Collections.sort(peerIds);
        return peerIds.isEmpty() ? "" : peerIds.get(0);
    }

    private byte[] encodeMigrationPayload(MigrationInfo info) {
        if (info == null) {
            return null;
        }

        String payload = safe(info.sessionId)
            + "|" + safe(info.newHostId)
            + "|" + info.maxClients
            + "|" + trimRoomName(info.roomName)
            + "|" + membershipEpoch;
        return payload.getBytes(StandardCharsets.UTF_8);
    }

    private MigrationInfo decodeMigrationPayload(String oldHostId, byte[] payloadBytes) {
        String payload = decodeControlPayload(payloadBytes);
        String[] parts = payload.split("\\|", 5);
        if (parts.length < 4) {
            return null;
        }

        MigrationInfo info = new MigrationInfo();
        info.oldHostId = safe(oldHostId);
        info.newHostId = safe(parts[1]);
        info.sessionId = safe(parts[0]);
        info.maxClients = Math.max(1, Math.min(7, parseInt(parts[2], maxClients)));
        info.roomName = trimRoomName(parts[3]);
        info.membershipEpoch = parts.length > 4 ? parseInt(parts[4], 0) : 0;
        info.transport = transport;
        info.becomingHost = info.newHostId.equals(localPeerId);
        return info;
    }

    private void startMigration(MigrationInfo info) {
        if (info == null || info.newHostId.isEmpty() || info.sessionId.isEmpty()) {
            finishLeave(null);
            nativeOnSessionEnded("migration_failed");
            return;
        }

        migration = info;
        migrationJoinInProgress = false;
        removeSessionPeer(info.oldHostId);
        addSessionPeer(localPeerId);
        addSessionPeer(info.newHostId);
        nativeOnSessionMigrating(info.oldHostId, info.newHostId);
        scheduleMigrationTimeout();
    }

    private boolean beginUnexpectedHostRecovery() {
        if (!"resilient".equals(transport)) {
            return false;
        }

        String oldHostId = safe(hostPeerId);
        if (oldHostId.isEmpty() || safe(joinedSessionId).isEmpty()) {
            return false;
        }

        removeSessionPeer(oldHostId);
        addSessionPeer(localPeerId);

        String successor = selectRecoverySuccessor(oldHostId);
        if (successor.isEmpty()) {
            return false;
        }

        MigrationInfo info = new MigrationInfo();
        info.oldHostId = oldHostId;
        info.newHostId = successor;
        info.sessionId = joinedSessionId;
        info.roomName = trimRoomName(joinedRoomName.isEmpty() ? roomName : joinedRoomName);
        info.transport = transport;
        info.maxClients = Math.max(1, Math.min(7, joinedMaxClients));
        info.becomingHost = successor.equals(localPeerId);

        bleLog("unexpected host loss recovery old_host=" + oldHostId
            + " new_host=" + successor
            + " session=" + safe(joinedSessionId)
            + " local=" + safe(localPeerId));

        startMigration(info);
        beginMigrationReconnect();
        return true;
    }

    private boolean hasActiveMigration() {
        return migration != null;
    }

    private boolean matchesMigrationRoom(RoomInfo room) {
        return migration != null
            && room != null
            && migration.sessionId.equals(room.sessionId)
            && migration.newHostId.equals(room.hostPeerId);
    }

    private void scheduleMigrationTimeout() {
        cancelMigrationTimeout();

        migrationTimeout = new Runnable() {
            @Override
            public void run() {
                migrationTimeout = null;
                if (migration == null) {
                    failMigration();
                    return;
                }

                // Convergence fallback: exclude failed successor and re-elect
                migration.excludedSuccessors.add(migration.newHostId);
                String nextSuccessor = selectRecoverySuccessorExcluding(migration.oldHostId, migration.excludedSuccessors);
                if (nextSuccessor.isEmpty()) {
                    failMigration();
                } else {
                    migration.newHostId = nextSuccessor;
                    migration.becomingHost = nextSuccessor.equals(localPeerId);
                    bleLog("convergence fallback new_host=" + nextSuccessor);
                    nativeOnSessionMigrating(migration.oldHostId, nextSuccessor);
                    beginMigrationReconnect();
                    scheduleMigrationTimeout();
                }
            }
        };

        handler.postDelayed(migrationTimeout, MIGRATION_TIMEOUT_MS);
    }

    private void cancelMigrationTimeout() {
        if (migrationTimeout != null) {
            handler.removeCallbacks(migrationTimeout);
            migrationTimeout = null;
        }
    }

    private void cancelPendingMigrationDeparture() {
        if (migrationDeparture != null) {
            handler.removeCallbacks(migrationDeparture);
            migrationDeparture = null;
        }
    }

    private void failMigration() {
        if (!hasActiveMigration()) {
            return;
        }

        cancelMigrationTimeout();
        finishLeave(null);
        nativeOnSessionEnded("migration_failed");
    }

    private void beginMigrationReconnect() {
        if (!hasActiveMigration()) {
            return;
        }

        if (migration.becomingHost) {
            if (!beginHostingSession(migration.roomName, migration.maxClients, migration.transport, migration.sessionId)) {
                failMigration();
            }
            return;
        }

        if (!scan()) {
            failMigration();
        }
    }

    private void completeMigrationResume() {
        if (!hasActiveMigration()) {
            return;
        }

        joinedSessionId = migration.sessionId;
        joinedRoomName = migration.roomName;
        joinedMaxClients = migration.maxClients;
        hostPeerId = migration.newHostId;
        membershipEpoch = migration.membershipEpoch;
        clientLocalEpoch = migration.membershipEpoch;
        if (migration.becomingHost) {
            joinedRoomId = "";
        }

        addSessionPeer(localPeerId);
        addSessionPeer(migration.newHostId);

        nativeOnSessionResumed(migration.sessionId, migration.newHostId);
        cancelMigrationTimeout();
        migration = null;
        migrationJoinInProgress = false;
        migrationDepartureInProgress = false;
    }

    // --- Client-side reconnect ---

    private boolean hasActiveReconnect() {
        return !reconnectSessionId.isEmpty();
    }

    private boolean matchesReconnectRoom(RoomInfo room) {
        return room != null
            && reconnectSessionId.equals(safe(room.sessionId))
            && reconnectHostPeerId.equals(safe(room.hostPeerId));
    }

    private boolean beginClientReconnect() {
        if (safe(joinedSessionId).isEmpty() || safe(hostPeerId).isEmpty()) {
            return false;
        }

        metricReconnectAttempt++;
        reconnectSessionId = joinedSessionId;
        reconnectHostPeerId = hostPeerId;
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;

        bleLog("beginClientReconnect session=" + safe(reconnectSessionId)
            + " host=" + safe(reconnectHostPeerId));

        nativeOnPeerStatus(localPeerId, "reconnecting");
        scheduleReconnectTimeout();

        if (!scan()) {
            failReconnect();
            return false;
        }

        reconnectScanInProgress = true;
        return true;
    }

    private void completeReconnectResume() {
        if (!hasActiveReconnect()) {
            return;
        }

        metricReconnectSuccess++;
        bleLog("completeReconnectResume session=" + safe(reconnectSessionId));

        cancelReconnectTimeout();
        reconnectSessionId = "";
        reconnectHostPeerId = "";
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;

        nativeOnPeerStatus(localPeerId, "connected");
    }

    private void failReconnect() {
        if (!hasActiveReconnect()) {
            return;
        }

        metricReconnectFail++;
        bleLog("failReconnect session=" + safe(reconnectSessionId));

        cancelReconnectTimeout();
        reconnectSessionId = "";
        reconnectHostPeerId = "";
        reconnectScanInProgress = false;
        reconnectJoinInProgress = false;

        stopScanInternal();
        finishLeave(null);
        nativeOnSessionEnded("host_lost");
    }

    private void scheduleReconnectTimeout() {
        cancelReconnectTimeout();

        reconnectTimeout = new Runnable() {
            @Override
            public void run() {
                reconnectTimeout = null;
                failReconnect();
            }
        };

        handler.postDelayed(reconnectTimeout, reconnectTimeoutMs);
    }

    private void cancelReconnectTimeout() {
        if (reconnectTimeout != null) {
            handler.removeCallbacks(reconnectTimeout);
            reconnectTimeout = null;
        }
    }

    // --- Host-side reconnect grace ---

    private void beginPeerReconnectGrace(String peerId) {
        metricGraceStart++;
        bleLog("beginPeerReconnectGrace peer=" + safe(peerId));

        rosterStatus.put(peerId, "reconnecting");
        membershipEpoch++;
        nativeOnPeerStatus(peerId, "reconnecting");
        broadcastRosterSnapshot();

        Runnable timeout = new Runnable() {
            @Override
            public void run() {
                peerReconnectTimeouts.remove(peerId);
                expirePeerReconnectGrace(peerId);
            }
        };

        peerReconnectTimeouts.put(peerId, timeout);
        handler.postDelayed(timeout, reconnectTimeoutMs);
    }

    private void expirePeerReconnectGrace(String peerId) {
        metricGraceExpire++;
        bleLog("expirePeerReconnectGrace peer=" + safe(peerId));
        removeSessionPeer(peerId);
        rosterStatus.remove(peerId);
        membershipEpoch++;
        nativeOnPeerLeft(peerId, "timeout");
        notifyPeerLeft(peerId, "timeout");
        broadcastRosterSnapshot();
        startAdvertising();
    }

    private void cancelPeerReconnectGrace(String peerId) {
        Runnable timeout = peerReconnectTimeouts.remove(peerId);
        if (timeout != null) {
            handler.removeCallbacks(timeout);
        }
    }

    private void cancelAllPeerReconnectGraces() {
        for (Runnable timeout : peerReconnectTimeouts.values()) {
            handler.removeCallbacks(timeout);
        }
        peerReconnectTimeouts.clear();
    }

    private boolean isPeerInReconnectGrace(String peerId) {
        return peerReconnectTimeouts.containsKey(peerId);
    }

    private void completeLocalJoin() {
        addSessionPeer(localPeerId);
        addSessionPeer(hostPeerId);
        clientPendingHelloAck = true;

        String joinIntent;
        if (reconnectJoinInProgress && hasActiveReconnect()) {
            joinIntent = "reconnect";
        } else if (migrationJoinInProgress && hasActiveMigration()) {
            joinIntent = "migration_resume";
        } else {
            joinIntent = "fresh";
        }

        String helloSessionId = "fresh".equals(joinIntent) && safe(joinedSessionId).isEmpty() ? "" : safe(joinedSessionId);
        String helloPayload = helloSessionId + "|" + joinIntent;

        bleLog("completeLocalJoin room=" + safe(joinedRoomId)
            + " session=" + safe(joinedSessionId)
            + " local=" + safe(localPeerId)
            + " host=" + safe(hostPeerId)
            + " transport=" + safe(transport)
            + " intent=" + joinIntent);

        metricCtrlOut++;
        writeToHost(encodePacket(PACKET_KIND_CONTROL, localPeerId, hostPeerId, CONTROL_HELLO, encodeControlPayload(helloPayload), 0));
    }

    private void handleJoinFailure(String detail) {
        bleLog("handleJoinFailure detail=" + safe(detail));
        clientLeaving = true;
        leaveClientOnly();

        if (reconnectJoinInProgress || hasActiveReconnect()) {
            reconnectJoinInProgress = false;
            reconnectScanInProgress = false;
            if (!scan()) {
                failReconnect();
            } else {
                reconnectScanInProgress = true;
            }
        } else if (migrationJoinInProgress || hasActiveMigration()) {
            failMigration();
        } else {
            nativeOnError("join_failed", detail);
        }
    }

    public boolean broadcast(String msgType, byte[] payload) {
        if (!isReady("send_failed")) {
            return false;
        }

        metricMsgOut++;
        byte[] packet = encodePacket(PACKET_KIND_DATA, localPeerId, "", msgType, payload, nextMessageId());
        if (hosting) {
            lastBroadcastPacket = packet;
            if (connectedClients.isEmpty()) {
                return true;
            }
            return notifyClients(packet, null);
        }

        return writeToHost(packet);
    }

    public boolean send(String peerId, String msgType, byte[] payload) {
        if (!isReady("send_failed")) {
            return false;
        }

        metricMsgOut++;
        byte[] packet = encodePacket(PACKET_KIND_DATA, localPeerId, safe(peerId), msgType, payload, nextMessageId());
        if (hosting) {
            BluetoothDevice device = connectedClients.get(peerId);
            if (device == null) {
                nativeOnError("send_failed", "Target peer is not connected.");
                return false;
            }
            return notifyClient(device, packet);
        }

        return writeToHost(packet);
    }

    private boolean isReady(String errorCode) {
        if (!hasBluetoothLE()) {
            nativeOnError("transport_unavailable", "Bluetooth LE is not available on this device.");
            return false;
        }
        if (!hasBluetoothPermissions()) {
            nativeOnError(errorCode, "Bluetooth permissions are missing.");
            return false;
        }
        if (!bluetoothAdapter.isEnabled()) {
            nativeOnError(errorCode, "Bluetooth is turned off.");
            return false;
        }
        return true;
    }

    private String generateShortId() {
        return UUID.randomUUID().toString().replace("-", "").substring(0, 6);
    }

    private String generateSessionId() {
        return generateShortId();
    }

    private String trimRoomName(String room) {
        if (room == null || room.isEmpty()) {
            return "Room";
        }

        String clean = room.replace('|', ' ').replace('\n', ' ').replace('\r', ' ').trim();
        if (clean.isEmpty()) {
            clean = "Room";
        }

        return clean.length() > 8 ? clean.substring(0, 8) : clean;
    }

    private boolean startAdvertising() {
        if (hosting && !hostServiceReady) {
            return false;
        }

        if (advertiser == null) {
            nativeOnError("host_failed", "Bluetooth advertiser is unavailable.");
            return false;
        }

        stopAdvertisingInternal();

        AdvertiseSettings settings = new AdvertiseSettings.Builder()
            .setAdvertiseMode(AdvertiseSettings.ADVERTISE_MODE_LOW_LATENCY)
            .setConnectable(true)
            .setTimeout(0)
            .build();

        AdvertiseData advertiseData = new AdvertiseData.Builder()
            .addServiceUuid(new ParcelUuid(SERVICE_UUID))
            .build();

        try {
            byte[] roomData = encodeRoomData();
            bleLog("advertise adv service_uuid=" + SERVICE_UUID + " manufacturer_data=<none>");
            bleLog("advertise scan_response manufacturer_id=0x" + Integer.toHexString(MANUFACTURER_DATA_ID).toUpperCase(Locale.US)
                + " payload=" + new String(roomData, StandardCharsets.UTF_8)
                + " hex=" + hexPreview(roomData));
            AdvertiseData scanResponse = new AdvertiseData.Builder()
                .addManufacturerData(MANUFACTURER_DATA_ID, roomData)
                .build();

            advertiser.startAdvertising(settings, advertiseData, scanResponse, advertiseCallback);
            return true;
        } catch (IllegalArgumentException | SecurityException e) {
            nativeOnError("host_failed", "Advertising setup failed: " + e.getMessage());
            return false;
        }
    }

    private void stopAdvertisingInternal() {
        if (advertiser != null) {
            advertiser.stopAdvertising(advertiseCallback);
        }
    }

    private void stopScanInternal() {
        if (scanner != null && scanning) {
            scanner.stopScan(scanCallback);
        }
        if (scanWatchdogShort != null) {
            handler.removeCallbacks(scanWatchdogShort);
            scanWatchdogShort = null;
        }
        if (scanWatchdogLong != null) {
            handler.removeCallbacks(scanWatchdogLong);
            scanWatchdogLong = null;
        }
        scanning = false;
    }

    private void scheduleScanDiagnostics() {
        if (scanWatchdogShort != null) {
            handler.removeCallbacks(scanWatchdogShort);
        }
        if (scanWatchdogLong != null) {
            handler.removeCallbacks(scanWatchdogLong);
        }

        scanWatchdogShort = () -> {
            if (!scanning) {
                return;
            }

            bleLog("scan watchdog after_ms=1500 callbacks=" + scanResultCount
                + " adapter_enabled=" + (bluetoothAdapter != null && bluetoothAdapter.isEnabled())
                + " scanner=" + (scanner != null));
        };

        scanWatchdogLong = () -> {
            if (!scanning) {
                return;
            }

            bleLog("scan watchdog after_ms=5000 callbacks=" + scanResultCount
                + " adapter_enabled=" + (bluetoothAdapter != null && bluetoothAdapter.isEnabled())
                + " scanner=" + (scanner != null));
        };

        handler.postDelayed(scanWatchdogShort, 1500L);
        handler.postDelayed(scanWatchdogLong, 5000L);
    }

    private void leaveHostOnly() {
        connectedClients.clear();
        pendingClients.clear();
        pendingClientTimestamps.clear();
        devicePeerIds.clear();
        deviceMtu.clear();
        notificationQueues.clear();
        inboundAssemblies.clear();
        hostServiceReady = false;

        if (gattServer != null) {
            gattServer.close();
            gattServer = null;
        }

        serverMessageCharacteristic = null;
    }

    private void leaveClientOnly() {
        clientJoined = false;
        clientWriteQueue.clear();
        clientWriteInFlight = false;
        clientMtu = DEFAULT_ATT_MTU;
        inboundAssemblies.clear();

        if (clientGatt != null) {
            clientGatt.disconnect();
            clientGatt.close();
            clientGatt = null;
        }

        clientMessageCharacteristic = null;
    }

    private byte[] encodeRoomData() {
        String payload = ROOM_DISCOVERY_PREFIX
            + shortenId(sessionId)
            + shortenId(localPeerId)
            + encodeTransport(transport)
            + Math.max(1, Math.min(7, maxClients))
            + Math.max(0, Math.min(9, connectedClients.size()))
            + trimRoomName(roomName);
        byte[] bytes = payload.getBytes(StandardCharsets.UTF_8);
        bleLog("encodeRoom payload=" + payload + " hex=" + hexPreview(bytes));
        return bytes;
    }

    private RoomInfo decodeRoom(ScanResult result) {
        ScanRecord record = result.getScanRecord();
        if (record == null) {
            return null;
        }

        byte[] manufacturerData = record.getManufacturerSpecificData(MANUFACTURER_DATA_ID);
        if (manufacturerData != null && manufacturerData.length > 0) {
            bleLog("scan manufacturer payload=" + new String(manufacturerData, StandardCharsets.UTF_8) + " hex=" + hexPreview(manufacturerData));
            RoomInfo room = decodeRoomFromCompactPayload(new String(manufacturerData, StandardCharsets.UTF_8), result);
            if (room != null) {
                return room;
            }
        }

        byte[] serviceData = record.getServiceData(new ParcelUuid(SERVICE_UUID));
        if (serviceData != null && serviceData.length > 0) {
            bleLog("scan service_data hex=" + hexPreview(serviceData));
            RoomInfo room = decodeRoomFromCompactPayload(new String(serviceData, StandardCharsets.UTF_8), result);
            if (room != null) {
                return room;
            }
        }

        bleLog("scan local_name payload=" + safe(record.getDeviceName()));
        return decodeRoomFromLocalName(record.getDeviceName(), result);
    }

    private RoomInfo decodeRoomFromCompactPayload(String payload, ScanResult result) {
        if (payload == null || payload.isEmpty()) {
            return null;
        }

        if (payload.startsWith(ROOM_DISCOVERY_PREFIX)) {
            return decodeRoomFromLocalName(payload, result);
        }

        String[] parts = payload.split("\\|", 6);
        if (parts.length < 6) {
            return null;
        }

        RoomInfo room = new RoomInfo();
        room.roomId = safeDeviceKey(result.getDevice());
        room.sessionId = parts[0];
        room.hostPeerId = parts[1];
        room.transport = decodeTransport(parts[2]);
        room.maxClients = parseInt(parts[3], 4);
        room.peerCount = parseInt(parts[4], 0);
        room.name = parts[5];
        room.rssi = result.getRssi();
        room.device = result.getDevice();
        bleLog("decodeRoom compact " + roomSummary(room));
        return room;
    }

    private String shortenId(String value) {
        String clean = safe(value);
        if (clean.length() <= SHORT_ID_LENGTH) {
            return clean;
        }

        return clean.substring(0, SHORT_ID_LENGTH);
    }

    private RoomInfo decodeRoomFromLocalName(String localName, ScanResult result) {
        if (localName == null || !localName.startsWith(ROOM_DISCOVERY_PREFIX)) {
            return null;
        }

        int minimumLength = ROOM_DISCOVERY_PREFIX.length() + SHORT_ID_LENGTH + SHORT_ID_LENGTH + 3;
        if (localName.length() < minimumLength) {
            return null;
        }

        int offset = ROOM_DISCOVERY_PREFIX.length();

        RoomInfo room = new RoomInfo();
        room.roomId = safeDeviceKey(result.getDevice());
        room.sessionId = localName.substring(offset, offset + SHORT_ID_LENGTH);
        offset += SHORT_ID_LENGTH;

        room.hostPeerId = localName.substring(offset, offset + SHORT_ID_LENGTH);
        offset += SHORT_ID_LENGTH;

        room.transport = decodeTransport(localName.substring(offset, offset + 1));
        offset += 1;

        room.maxClients = parseInt(localName.substring(offset, offset + 1), 4);
        offset += 1;

        room.peerCount = parseInt(localName.substring(offset, offset + 1), 0);
        offset += 1;

        room.name = localName.substring(offset);
        room.rssi = result.getRssi();
        room.device = result.getDevice();
        bleLog("decodeRoom local_name " + roomSummary(room));
        return room;
    }

    private int parseInt(String value, int fallback) {
        try {
            return Integer.parseInt(value);
        } catch (NumberFormatException ignored) {
            return fallback;
        }
    }

    private String encodeTransport(String value) {
        return "resilient".equals(value) ? "s" : "r";
    }

    private String decodeTransport(String value) {
        return "s".equals(value) ? "resilient" : "reliable";
    }

    private boolean validateInboundPacketShape(Packet packet, String context) {
        if (packet == null) {
            bleLog("reject packet context=" + safe(context) + " reason=null_packet");
            return false;
        }

        String kind = safe(packet.kind);
        String msgType = safe(packet.msgType);
        String fromPeerId = safe(packet.fromPeerId);

        if (kind.isEmpty()) {
            bleLog("reject packet context=" + safe(context) + " reason=missing_kind");
            return false;
        }

        if (msgType.isEmpty()) {
            bleLog("reject packet context=" + safe(context) + " reason=missing_type kind=" + kind);
            return false;
        }

        if (PACKET_KIND_DATA.equals(kind) && fromPeerId.isEmpty()) {
            bleLog("reject packet context=" + safe(context)
                + " reason=missing_sender kind=" + kind
                + " type=" + msgType);
            return false;
        }

        return true;
    }

    private boolean validateControlPacketPayload(Packet packet, String context) {
        String msgType = safe(packet.msgType);

        if (CONTROL_PEER_JOINED.equals(msgType) || CONTROL_HELLO_ACK.equals(msgType)) {
            if (safePayload(packet.payload).length != 0) {
                bleLog("reject packet context=" + safe(context)
                    + " reason=unexpected_payload type=" + msgType);
                return false;
            }
        } else if (CONTROL_SESSION_MIGRATING.equals(msgType)) {
            if (safePayload(packet.payload).length == 0) {
                bleLog("reject packet context=" + safe(context)
                    + " reason=missing_payload type=" + msgType);
                return false;
            }

            MigrationInfo info = decodeMigrationPayload(packet.fromPeerId, packet.payload);
            if (info == null || safe(info.sessionId).isEmpty() || safe(info.newHostId).isEmpty()) {
                bleLog("reject packet context=" + safe(context)
                    + " reason=invalid_migration_payload type=" + msgType);
                return false;
            }
        }

        return true;
    }

    private boolean validateInboundPacketFromDevice(Packet packet, String deviceKey) {
        if (!validateInboundPacketShape(packet, "device:" + safe(deviceKey))) {
            return false;
        }

        String msgType = safe(packet.msgType);
        String fromPeerId = safe(packet.fromPeerId);
        String toPeerId = safe(packet.toPeerId);
        String boundPeerId = devicePeerIds.get(deviceKey);

        if (PACKET_KIND_CONTROL.equals(packet.kind) && CONTROL_HELLO.equals(msgType)) {
            if (!validateControlPacketPayload(packet, "device:" + safe(deviceKey))) {
                return false;
            }

            if (fromPeerId.isEmpty()) {
                bleLog("reject packet context=device:" + safe(deviceKey) + " reason=hello_missing_peer");
                return false;
            }

            if (!toPeerId.isEmpty() && !toPeerId.equals(localPeerId)) {
                bleLog("reject packet context=device:" + safe(deviceKey)
                    + " reason=hello_wrong_target target=" + toPeerId
                    + " local=" + safe(localPeerId));
                return false;
            }

            if (boundPeerId != null && !boundPeerId.equals(fromPeerId)) {
                bleLog("reject packet context=device:" + safe(deviceKey)
                    + " reason=sender_spoof claimed=" + fromPeerId
                    + " bound=" + boundPeerId);
                return false;
            }

            BluetoothDevice existingDevice = connectedClients.get(fromPeerId);
            if (existingDevice != null && !safeDeviceKey(existingDevice).equals(safe(deviceKey))) {
                bleLog("reject packet context=device:" + safe(deviceKey)
                    + " reason=peer_already_bound peer=" + fromPeerId
                    + " existing=" + safeDeviceKey(existingDevice));
                return false;
            }

            return true;
        }

        if (boundPeerId == null) {
            bleLog("reject packet context=device:" + safe(deviceKey)
                + " reason=packet_before_hello type=" + msgType);
            return false;
        }

        if (fromPeerId.isEmpty() || !boundPeerId.equals(fromPeerId)) {
            bleLog("reject packet context=device:" + safe(deviceKey)
                + " reason=sender_spoof claimed=" + fromPeerId
                + " bound=" + boundPeerId);
            return false;
        }

        return true;
    }

    private boolean validateInboundPacketFromHost(Packet packet) {
        if (!validateInboundPacketShape(packet, "host")) {
            return false;
        }

        if (PACKET_KIND_CONTROL.equals(packet.kind) && !validateControlPacketPayload(packet, "host")) {
            return false;
        }

        String msgType = safe(packet.msgType);
        String fromPeerId = safe(packet.fromPeerId);

        if (PACKET_KIND_CONTROL.equals(packet.kind)
            && (CONTROL_SESSION_MIGRATING.equals(msgType) || CONTROL_SESSION_ENDED.equals(msgType))
            && !safe(hostPeerId).isEmpty()
            && !safe(hostPeerId).equals(fromPeerId)) {
            bleLog("reject packet context=host reason=host_control_sender_mismatch type=" + msgType
                + " claimed=" + fromPeerId
                + " host=" + safe(hostPeerId));
            return false;
        }

        return true;
    }

    private byte[] encodePacket(String kind, String fromPeerId, String toPeerId, String msgType, byte[] payload, int messageId) {
        try {
            ByteArrayOutputStream bytes = new ByteArrayOutputStream();
            DataOutputStream out = new DataOutputStream(bytes);
            out.writeByte(PACKET_VERSION);
            out.writeShort(messageId);
            writeString(out, kind);
            writeString(out, fromPeerId);
            writeString(out, toPeerId);
            writeString(out, msgType);
            writeBytes(out, payload);
            out.flush();
            byte[] encoded = bytes.toByteArray();
            bleLog("encodePacket raw_len=" + encoded.length + " msgId=" + messageId + " " + packetSummary(kind, fromPeerId, toPeerId, msgType, payload));
            return encoded;
        } catch (IOException e) {
            return new byte[0];
        }
    }

    private Packet decodePacket(byte[] packetBytes) {
        if (packetBytes == null || packetBytes.length == 0) {
            return null;
        }

        try {
            DataInputStream in = new DataInputStream(new ByteArrayInputStream(packetBytes));
            int version = in.readUnsignedByte();
            if (version != PACKET_VERSION) {
                throw new IOException("Unsupported packet version.");
            }

            Packet packet = new Packet();
            packet.messageId = in.readUnsignedShort();
            packet.kind = readString(in);
            packet.fromPeerId = readString(in);
            packet.toPeerId = readString(in);
            packet.msgType = readString(in);
            packet.payload = readBytes(in);
            bleLog("decodePacket raw_len=" + packetBytes.length + " msgId=" + packet.messageId + " " + packetSummary(packet));
            return packet;
        } catch (IOException e) {
            nativeOnError("invalid_payload", "Received malformed BLE packet.");
            return null;
        }
    }

    private void writeString(DataOutputStream out, String value) throws IOException {
        byte[] bytes = safe(value).getBytes(StandardCharsets.UTF_8);
        out.writeInt(bytes.length);
        out.write(bytes);
    }

    private void writeBytes(DataOutputStream out, byte[] value) throws IOException {
        byte[] bytes = safePayload(value);
        out.writeInt(bytes.length);
        out.write(bytes);
    }

    private String readString(DataInputStream in) throws IOException {
        int len = in.readInt();
        if (len < 0 || len > 4096) {
            throw new IOException("Field length out of range.");
        }

        byte[] bytes = new byte[len];
        in.readFully(bytes);
        return new String(bytes, StandardCharsets.UTF_8);
    }

    private byte[] readBytes(DataInputStream in) throws IOException {
        int len = in.readInt();
        if (len < 0 || len > 65536) {
            throw new IOException("Payload length out of range.");
        }

        byte[] bytes = new byte[len];
        in.readFully(bytes);
        return bytes;
    }

    private int getPayloadLimitForMtu(int mtu) {
        return Math.max(1, mtu - ATT_PAYLOAD_OVERHEAD);
    }

    private int nextNonce() {
        int nonce = nextMessageNonce & 0xFFFF;
        nextMessageNonce = (nextMessageNonce + 1) & 0xFFFF;
        if (nextMessageNonce == 0) {
            nextMessageNonce = 1;
        }
        return nonce;
    }

    private int nextMessageId() {
        int id = nextMessageId & 0xFFFF;
        nextMessageId = (nextMessageId + 1) & 0xFFFF;
        if (nextMessageId == 0) {
            nextMessageId = 1;
        }
        return id;
    }

    private ArrayList<byte[]> fragmentPacket(byte[] packetBytes, int payloadLimit) {
        byte[] bytes = safePayload(packetBytes);
        int chunkSize = payloadLimit - FRAGMENT_HEADER_SIZE;
        if (chunkSize <= 0) {
            nativeOnError("send_failed", "BLE payload limit is too small for transport framing.");
            return null;
        }

        int fragmentCount = (bytes.length + chunkSize - 1) / chunkSize;
        if (fragmentCount <= 0) {
            fragmentCount = 1;
        }

        if (fragmentCount > MAX_FRAGMENT_COUNT) {
            nativeOnError("payload_too_large", "BLE payload exceeds the current transport limit.");
            return null;
        }

        int nonce = nextNonce();
        ArrayList<byte[]> fragments = new ArrayList<>(fragmentCount);

        for (int index = 0; index < fragmentCount; index++) {
            int start = index * chunkSize;
            int end = Math.min(start + chunkSize, bytes.length);
            int len = Math.max(0, end - start);
            byte[] fragment = new byte[FRAGMENT_HEADER_SIZE + len];
            fragment[0] = (byte) FRAGMENT_VERSION;
            fragment[1] = (byte) ((nonce >> 8) & 0xFF);
            fragment[2] = (byte) (nonce & 0xFF);
            fragment[3] = (byte) index;
            fragment[4] = (byte) fragmentCount;
            if (len > 0) {
                System.arraycopy(bytes, start, fragment, FRAGMENT_HEADER_SIZE, len);
            }
            fragments.add(fragment);
        }

        metricFragmentTx += fragmentCount;
        bleLog("fragmentPacket payload_limit=" + payloadLimit
            + " raw_len=" + bytes.length
            + " nonce=" + nonce
            + " fragments=" + fragmentCount
            + " first_fragment=" + (fragments.isEmpty() ? "<none>" : hexPreview(fragments.get(0))));
        return fragments;
    }

    private void pruneInboundAssemblies() {
        long nowMs = System.currentTimeMillis();
        ArrayList<String> expired = new ArrayList<>();

        for (Map.Entry<String, InboundAssembly> entry : inboundAssemblies.entrySet()) {
            if (entry.getValue().updatedAtMs + ASSEMBLY_TIMEOUT_MS < nowMs) {
                expired.add(entry.getKey());
            }
        }

        for (int i = 0; i < expired.size(); i++) {
            metricAssemblyTimeout++;
            String assemblyKey = expired.get(i);
            int split = assemblyKey.lastIndexOf(':');
            String sourceKey = split >= 0 ? assemblyKey.substring(0, split) : assemblyKey;
            int nonce = 0;
            if (split >= 0 && split + 1 < assemblyKey.length()) {
                try {
                    nonce = Integer.parseInt(assemblyKey.substring(split + 1));
                } catch (NumberFormatException ignored) {
                    nonce = 0;
                }
            }
            discardAssembly(assemblyKey, sourceKey, nonce, "stale_timeout", false, null);
        }
    }

    private void discardAssembly(String assemblyKey, String sourceKey, int nonce, String reason, boolean emitError, String detail) {
        InboundAssembly assembly = inboundAssemblies.remove(assemblyKey);
        if (assembly == null) {
            return;
        }

        bleLog("resetAssembly source=" + safe(sourceKey)
            + " nonce=" + nonce
            + " reason=" + safe(reason)
            + " received=" + assembly.receivedCount + "/" + assembly.fragmentCount
            + " bytes=" + assembly.totalBytes);

        if (!emitError || detail == null || detail.isEmpty()) {
            return;
        }

        nativeOnError(detail.contains("payload exceeds") ? "payload_too_large" : "invalid_payload", detail);
    }

    private ReassembledPacket processIncomingFragment(String sourceKey, byte[] fragmentBytes) {
        if (fragmentBytes == null || fragmentBytes.length < FRAGMENT_HEADER_SIZE) {
            return null;
        }

        metricFragmentRx++;
        pruneInboundAssemblies();

        int version = fragmentBytes[0] & 0xFF;
        if (version != FRAGMENT_VERSION) {
            metricFragmentDrop++;
            return null;
        }

        int nonce = ((fragmentBytes[1] & 0xFF) << 8) | (fragmentBytes[2] & 0xFF);
        int index = fragmentBytes[3] & 0xFF;
        int count = fragmentBytes[4] & 0xFF;
        bleLog("incomingFragment source=" + safe(sourceKey)
            + " nonce=" + nonce
            + " index=" + index + "/" + count
            + " raw_len=" + fragmentBytes.length
            + " hex=" + hexPreview(fragmentBytes));

        if (count == 0 || index >= count) {
            metricFragmentDrop++;
            return null;
        }

        byte[] chunk = Arrays.copyOfRange(fragmentBytes, FRAGMENT_HEADER_SIZE, fragmentBytes.length);
        if (count == 1) {
            String singleKey = sourceKey + ":" + nonce;
            if (inboundAssemblies.containsKey(singleKey)) {
                discardAssembly(singleKey, sourceKey, nonce, "single_fragment_replaced_partial", false, null);
            }
            return new ReassembledPacket(chunk, nonce);
        }

        String assemblyKey = sourceKey + ":" + nonce;
        InboundAssembly assembly = inboundAssemblies.get(assemblyKey);
        if (assembly == null) {
            // Enforce per-source assembly limit
            String sourcePrefix = sourceKey + ":";
            int sourceCount = 0;
            String oldestKey = null;
            long oldestTime = Long.MAX_VALUE;
            for (Map.Entry<String, InboundAssembly> entry : inboundAssemblies.entrySet()) {
                if (entry.getKey().startsWith(sourcePrefix)) {
                    sourceCount++;
                    if (entry.getValue().updatedAtMs < oldestTime) {
                        oldestTime = entry.getValue().updatedAtMs;
                        oldestKey = entry.getKey();
                    }
                }
            }
            if (sourceCount >= MAX_ASSEMBLIES_PER_SOURCE && oldestKey != null) {
                discardAssembly(oldestKey, sourceKey, 0, "max_assemblies_exceeded", false, null);
            }

            assembly = new InboundAssembly();
            assembly.fragmentCount = count;
            assembly.fragments = new byte[count][];
            inboundAssemblies.put(assemblyKey, assembly);
        } else if (assembly.fragmentCount != count) {
            discardAssembly(assemblyKey, sourceKey, nonce, "fragment_count_mismatch", true,
                "Received BLE transport fragments with mismatched counts.");
            return null;
        }

        assembly.updatedAtMs = System.currentTimeMillis();
        if (assembly.fragments[index] == null) {
            assembly.fragments[index] = chunk;
            assembly.receivedCount += 1;
            assembly.totalBytes += chunk.length;
        } else if (!Arrays.equals(assembly.fragments[index], chunk)) {
            discardAssembly(assemblyKey, sourceKey, nonce, "conflicting_duplicate_fragment", true,
                "Received BLE transport fragments with conflicting duplicate data.");
            return null;
        } else {
            bleLog("duplicateFragment source=" + safe(sourceKey)
                + " nonce=" + nonce
                + " index=" + index + "/" + count
                + " action=ignored");
        }

        if (assembly.totalBytes > MAX_REASSEMBLED_PACKET_SIZE) {
            discardAssembly(assemblyKey, sourceKey, nonce, "assembly_overflow", true,
                "Received BLE payload exceeds the supported transport limit.");
            return null;
        }

        if (assembly.receivedCount < assembly.fragmentCount) {
            return null;
        }

        byte[] packetBytes = new byte[assembly.totalBytes];
        int offset = 0;
        for (int i = 0; i < assembly.fragmentCount; i++) {
            byte[] part = assembly.fragments[i];
            if (part == null) {
                discardAssembly(assemblyKey, sourceKey, nonce, "incomplete_reassembly", true,
                    "Received incomplete BLE transport payload.");
                return null;
            }

            System.arraycopy(part, 0, packetBytes, offset, part.length);
            offset += part.length;
        }

        inboundAssemblies.remove(assemblyKey);
        bleLog("reassembledPacket source=" + safe(sourceKey)
            + " nonce=" + nonce
            + " raw_len=" + packetBytes.length
            + " hex=" + hexPreview(packetBytes));
        return new ReassembledPacket(packetBytes, nonce);
    }

    private boolean pumpClientWriteQueue() {
        if (clientWriteInFlight) {
            return true;
        }

        if (clientGatt == null || clientMessageCharacteristic == null) {
            return false;
        }

        byte[] fragment = clientWriteQueue.peekFirst();
        if (fragment == null) {
            return true;
        }

        try {
            clientMessageCharacteristic.setValue(fragment);
            if (!clientGatt.writeCharacteristic(clientMessageCharacteristic)) {
                clientWriteQueue.clear();
                nativeOnError("send_failed", "Could not queue BLE write to host.");
                return false;
            }
        } catch (SecurityException e) {
            clientWriteQueue.clear();
            nativeOnError("send_failed", "Bluetooth permission was lost.");
            return false;
        }

        clientWriteInFlight = true;
        return true;
    }

    private boolean enqueueClientPacket(byte[] packetBytes) {
        Packet packet = decodePacket(packetBytes);
        if (packet != null) {
            bleLog("client enqueuePacket " + packetSummary(packet));
        }
        ArrayList<byte[]> fragments = fragmentPacket(packetBytes, getPayloadLimitForMtu(clientMtu));
        if (fragments == null) {
            return false;
        }

        for (int i = 0; i < fragments.size(); i++) {
            clientWriteQueue.addLast(fragments.get(i));
        }

        return pumpClientWriteQueue();
    }

    private boolean pumpNotificationQueue(BluetoothDevice device) {
        if (device == null || gattServer == null || serverMessageCharacteristic == null) {
            return false;
        }

        String deviceKey = safeDeviceKey(device);
        ArrayDeque<byte[]> queue = notificationQueues.get(deviceKey);
        if (queue == null || queue.isEmpty()) {
            return true;
        }

        try {
            serverMessageCharacteristic.setValue(queue.peekFirst());
            if (!gattServer.notifyCharacteristicChanged(device, serverMessageCharacteristic, false)) {
                notificationQueues.remove(deviceKey);
                nativeOnError("send_failed", "Could not queue BLE notification.");
                return false;
            }
        } catch (SecurityException e) {
            notificationQueues.remove(deviceKey);
            nativeOnError("send_failed", "Bluetooth permission was lost.");
            return false;
        }

        return true;
    }

    private boolean enqueueNotificationPacket(BluetoothDevice device, byte[] packetBytes) {
        if (device == null) {
            return false;
        }

        Packet packet = decodePacket(packetBytes);
        if (packet != null) {
            bleLog("host enqueueNotification device=" + safeDeviceKey(device) + " " + packetSummary(packet));
        }

        String deviceKey = safeDeviceKey(device);
        int mtu = deviceMtu.containsKey(deviceKey) ? deviceMtu.get(deviceKey) : DEFAULT_ATT_MTU;
        ArrayList<byte[]> fragments = fragmentPacket(packetBytes, getPayloadLimitForMtu(mtu));
        if (fragments == null) {
            return false;
        }

        ArrayDeque<byte[]> queue = notificationQueues.get(deviceKey);
        if (queue == null) {
            queue = new ArrayDeque<>();
            notificationQueues.put(deviceKey, queue);
        }

        boolean wasIdle = queue.isEmpty();
        for (int i = 0; i < fragments.size(); i++) {
            queue.addLast(fragments.get(i));
        }

        return !wasIdle || pumpNotificationQueue(device);
    }

    private boolean writeToHost(byte[] packet) {
        if (clientGatt == null || clientMessageCharacteristic == null) {
            nativeOnError("send_failed", "No active BLE connection.");
            return false;
        }

        return enqueueClientPacket(packet);
    }

    private boolean notifyClient(BluetoothDevice device, byte[] packet) {
        if (device == null || gattServer == null || serverMessageCharacteristic == null) {
            return false;
        }

        return enqueueNotificationPacket(device, packet);
    }

    private boolean notifyClients(byte[] packet, String skipPeerId) {
        if (gattServer == null || serverMessageCharacteristic == null || connectedClients.isEmpty()) {
            return false;
        }

        boolean notified = false;

        for (Map.Entry<String, BluetoothDevice> entry : connectedClients.entrySet()) {
            if (skipPeerId != null && skipPeerId.equals(entry.getKey())) {
                continue;
            }
            notified |= notifyClient(entry.getValue(), packet);
        }

        return notified;
    }

    private void notifyClientsSessionEnded(String reason) {
        if (!hosting) {
            return;
        }

        metricCtrlOut++;
        notifyClients(encodePacket(PACKET_KIND_CONTROL, hostPeerId, "", CONTROL_SESSION_ENDED, encodeControlPayload(reason), 0), null);
    }

    private void notifyPeerJoined(String peerId) {
        metricCtrlOut++;
        byte[] packet = encodePacket(PACKET_KIND_CONTROL, peerId, "", CONTROL_PEER_JOINED, new byte[0], 0);
        notifyClients(packet, peerId);
    }

    private void notifyPeerLeft(String peerId, String reason) {
        metricCtrlOut++;
        byte[] packet = encodePacket(PACKET_KIND_CONTROL, peerId, "", CONTROL_PEER_LEFT, encodeControlPayload(reason), 0);
        notifyClients(packet, peerId);
    }

    private void handleHelloFromClient(BluetoothDevice device, String deviceKey, Packet packet) {
        String peerId = safe(packet.fromPeerId);
        if (peerId.isEmpty()) {
            disconnectDevice(device);
            return;
        }

        // Parse HELLO payload: sessionId|joinIntent
        String helloPayload = decodeControlPayload(packet.payload);
        String[] parts = helloPayload.split("\\|", 2);
        String helloSessionId = parts.length > 0 ? safe(parts[0]) : "";
        String joinIntent = parts.length > 1 ? safe(parts[1]) : "fresh";

        bleLog("received HELLO from peer=" + peerId + " device=" + deviceKey
            + " session=" + helloSessionId + " intent=" + joinIntent);

        // Validate admission
        if (connectedClients.size() >= maxClients && !isPeerInReconnectGrace(peerId)) {
            sendJoinRejected(device, peerId, "room_full");
            return;
        }
        if (connectedClients.containsKey(peerId)) {
            sendJoinRejected(device, peerId, "duplicate_peer_id");
            return;
        }
        if (!helloSessionId.isEmpty() && !helloSessionId.equals(safe(sessionId))) {
            sendJoinRejected(device, peerId, "stale_session");
            return;
        }
        if (!packet.toPeerId.isEmpty() && !packet.toPeerId.equals(safe(localPeerId))) {
            sendJoinRejected(device, peerId, "wrong_target");
            return;
        }
        if ("migration_resume".equals(joinIntent) && !migrationDepartureInProgress) {
            sendJoinRejected(device, peerId, "migration_mismatch");
            return;
        }

        // Admission granted
        pendingClients.remove(deviceKey);
        pendingClientTimestamps.remove(deviceKey);
        devicePeerIds.put(deviceKey, peerId);
        connectedClients.put(peerId, device);

        // Send hello_ack
        metricCtrlOut++;
        notifyClient(device, encodePacket(PACKET_KIND_CONTROL, localPeerId, peerId, CONTROL_HELLO_ACK, new byte[0], 0));

        if (isPeerInReconnectGrace(peerId)) {
            metricGraceResume++;
            cancelPeerReconnectGrace(peerId);
            addSessionPeer(peerId);
            rosterStatus.put(peerId, "connected");
            membershipEpoch++;
            bleLog("peer reconnected peer=" + peerId + " epoch=" + membershipEpoch);
            nativeOnPeerStatus(peerId, "connected");
            broadcastRosterSnapshot();
        } else {
            addSessionPeer(peerId);
            rosterStatus.put(peerId, "connected");
            membershipEpoch++;
            bleLog("peer admitted peer=" + peerId + " epoch=" + membershipEpoch);
            nativeOnPeerJoined(peerId);
            notifyPeerJoined(peerId);
            broadcastRosterSnapshot();
        }
        startAdvertising();
    }

    private void sendJoinRejected(BluetoothDevice device, String peerId, String reason) {
        bleLog("join_rejected peer=" + peerId + " reason=" + reason);
        metricJoinReject++;
        metricCtrlOut++;
        notifyClient(device, encodePacket(PACKET_KIND_CONTROL, localPeerId, peerId, CONTROL_JOIN_REJECTED, encodeControlPayload(reason), 0));
        handler.postDelayed(() -> disconnectDevice(device), 200L);
    }

    private void disconnectDevice(BluetoothDevice device) {
        if (gattServer != null && device != null) {
            try {
                gattServer.cancelConnection(device);
            } catch (SecurityException ignored) {
            }
        }
    }

    private void handleRosterRequestFromClient(BluetoothDevice device, Packet packet) {
        if (device == null) return;
        String peerId = safe(packet.fromPeerId);
        BluetoothDevice clientDevice = connectedClients.get(peerId);
        if (clientDevice != null) {
            metricCtrlOut++;
            notifyClient(clientDevice, encodePacket(PACKET_KIND_CONTROL, localPeerId, peerId, CONTROL_ROSTER_SNAPSHOT, encodeRosterSnapshotPayload(), 0));
        }
    }

    private byte[] encodeRosterSnapshotPayload() {
        StringBuilder sb = new StringBuilder();
        sb.append(safe(sessionId)).append("|");
        sb.append(safe(localPeerId)).append("|");
        sb.append(membershipEpoch);
        for (Map.Entry<String, String> entry : rosterStatus.entrySet()) {
            sb.append("|").append(safe(entry.getKey())).append(":").append(safe(entry.getValue()));
        }
        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }

    private void broadcastRosterSnapshot() {
        byte[] payload = encodeRosterSnapshotPayload();
        metricCtrlOut++;
        notifyClients(encodePacket(PACKET_KIND_CONTROL, localPeerId, "", CONTROL_ROSTER_SNAPSHOT, payload, 0), null);
    }

    private void handleRosterSnapshot(byte[] payloadBytes) {
        String payload = decodeControlPayload(payloadBytes);
        String[] parts = payload.split("\\|");
        if (parts.length < 3) return;

        String snapshotSessionId = safe(parts[0]);
        String snapshotHostId = safe(parts[1]);
        int snapshotEpoch;
        try {
            snapshotEpoch = Integer.parseInt(parts[2]);
        } catch (NumberFormatException e) {
            return;
        }

        clientLocalEpoch = snapshotEpoch;
        rosterStatus.clear();

        HashSet<String> newPeers = new HashSet<>();
        for (int i = 3; i < parts.length; i++) {
            String[] peerParts = parts[i].split(":", 2);
            if (peerParts.length == 2) {
                String peerId = safe(peerParts[0]);
                String status = safe(peerParts[1]);
                if (!peerId.isEmpty()) {
                    rosterStatus.put(peerId, status);
                    newPeers.add(peerId);
                }
            }
        }

        // Detect joins and leaves compared to sessionPeerIds
        HashSet<String> currentPeers = new HashSet<>(sessionPeerIds);
        currentPeers.remove(localPeerId);
        currentPeers.remove(snapshotHostId);

        // Add host and self to session
        addSessionPeer(snapshotHostId);
        addSessionPeer(localPeerId);

        for (String peerId : newPeers) {
            if (!currentPeers.contains(peerId) && !peerId.equals(localPeerId) && !peerId.equals(snapshotHostId)) {
                addSessionPeer(peerId);
                nativeOnPeerJoined(peerId);
            }
        }

        for (String peerId : currentPeers) {
            if (!newPeers.contains(peerId) && !peerId.equals(snapshotHostId)) {
                removeSessionPeer(peerId);
                nativeOnPeerLeft(peerId, "roster_update");
            }
        }

        // Emit peer_status for reconnecting peers
        for (Map.Entry<String, String> entry : rosterStatus.entrySet()) {
            if ("reconnecting".equals(entry.getValue())) {
                nativeOnPeerStatus(entry.getKey(), "reconnecting");
            }
        }

        bleLog("handleRosterSnapshot session=" + snapshotSessionId
            + " host=" + snapshotHostId
            + " epoch=" + snapshotEpoch
            + " peers=" + newPeers.size());
    }

    private int computeRosterFingerprint() {
        ArrayList<String> entries = new ArrayList<>();
        for (Map.Entry<String, String> entry : rosterStatus.entrySet()) {
            String status = "connected".equals(entry.getValue()) ? "c" : "r";
            entries.add(safe(entry.getKey()) + ":" + status);
        }
        Collections.sort(entries);
        String joined = String.join("|", entries);
        java.util.zip.CRC32 crc = new java.util.zip.CRC32();
        crc.update(joined.getBytes(StandardCharsets.UTF_8));
        return (int) crc.getValue();
    }

    private void handleHeartbeatFingerprint(byte[] payload) {
        metricHeartbeatRx++;
        if (payload == null || payload.length < 4) return;
        int remoteFingerprint = ((payload[0] & 0xFF) << 24) | ((payload[1] & 0xFF) << 16)
            | ((payload[2] & 0xFF) << 8) | (payload[3] & 0xFF);
        int localFingerprint = computeRosterFingerprint();
        if (remoteFingerprint != localFingerprint) {
            long now = System.currentTimeMillis();
            long interval = (long) (reliabilityHeartbeatInterval * 1000);
            if (now - lastRosterRequestMs >= interval) {
                lastRosterRequestMs = now;
                metricRosterRequest++;
                metricCtrlOut++;
                writeToHost(encodePacket(PACKET_KIND_CONTROL, localPeerId, hostPeerId, CONTROL_ROSTER_REQUEST, new byte[0], 0));
            }
        }
    }

    private String safe(String value) {
        return value == null ? "" : value;
    }

    private byte[] safePayload(byte[] value) {
        return value == null ? new byte[0] : value;
    }

    private byte[] encodeControlPayload(String value) {
        return safe(value).getBytes(StandardCharsets.UTF_8);
    }

    private String decodeControlPayload(byte[] value) {
        return new String(safePayload(value), StandardCharsets.UTF_8);
    }

    private String safeDeviceKey(BluetoothDevice device) {
        if (device == null) {
            return "";
        }

        try {
            return safe(device.getAddress());
        } catch (SecurityException e) {
            return "";
        }
    }

    private boolean isActiveClientGatt(BluetoothGatt gatt, String source, boolean closeIfStale) {
        if (gatt != null && gatt == clientGatt) {
            return true;
        }

        bleLog(source + " ignored stale_gatt=1");
        if (closeIfStale && gatt != null) {
            gatt.close();
        }
        return false;
    }

    private boolean isLocationEnabled() {
        try {
            LocationManager locationManager = (LocationManager) activity.getSystemService(Context.LOCATION_SERVICE);
            if (locationManager == null) {
                return false;
            }

            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.P) {
                return locationManager.isLocationEnabled();
            }

            return locationManager.isProviderEnabled(LocationManager.GPS_PROVIDER)
                || locationManager.isProviderEnabled(LocationManager.NETWORK_PROVIDER);
        } catch (Exception e) {
            return false;
        }
    }

    private void logScanEnvironment(String source) {
        bleLog(source
            + " env sdk=" + Build.VERSION.SDK_INT
            + " radio=" + getRadioState()
            + " permissions=" + hasBluetoothPermissions()
            + " location_enabled=" + isLocationEnabled()
            + " adapter_enabled=" + (bluetoothAdapter != null && bluetoothAdapter.isEnabled())
            + " scanner=" + (scanner != null)
            + " offloaded_filtering=" + (bluetoothAdapter != null && bluetoothAdapter.isOffloadedFilteringSupported())
            + " offloaded_batching=" + (bluetoothAdapter != null && bluetoothAdapter.isOffloadedScanBatchingSupported()));
    }

    private final AdvertiseCallback advertiseCallback = new AdvertiseCallback() {
        @Override
        public void onStartSuccess(AdvertiseSettings settingsInEffect) {
            if (hosting && !hostAnnounced) {
                hostAnnounced = true;
                if (hasActiveMigration() && migration.becomingHost) {
                    completeMigrationResume();
                } else {
                    nativeOnHosted(sessionId, localPeerId, transport);
                }
            }
        }

        @Override
        public void onStartFailure(int errorCode) {
            if (hasActiveMigration() && migration.becomingHost) {
                failMigration();
            } else {
                nativeOnError("host_failed", "Advertising failed with code " + errorCode + ".");
            }
        }
    };

    private final ScanCallback scanCallback = new ScanCallback() {
        @Override
        public void onScanResult(int callbackType, ScanResult result) {
            scanResultCount += 1;
            ScanRecord record = result != null ? result.getScanRecord() : null;
            bleLog("scan callback"
                + " callbackType=" + callbackType
                + " device=" + safeDeviceKey(result != null ? result.getDevice() : null)
                + " rssi=" + (result != null ? result.getRssi() : 0)
                + " name=" + safe(record != null ? record.getDeviceName() : "")
                + " has_record=" + (record != null));
            RoomInfo room = decodeRoom(result);
            if (room == null) {
                return;
            }

            bleLog("onScanResult callbackType=" + callbackType + " " + roomSummary(room));

            if (callbackType == ScanSettings.CALLBACK_TYPE_MATCH_LOST) {
                if (!hasActiveMigration() && rooms.remove(room.roomId) != null) {
                    nativeOnRoomLost(room.roomId);
                }
                return;
            }

            rooms.put(room.roomId, room);
            if (hasActiveMigration() && matchesMigrationRoom(room) && !migration.becomingHost && clientGatt == null) {
                connectToRoom(room.roomId, room, true);
                return;
            }

            if (hasActiveMigration()) {
                return;
            }

            if (hasActiveReconnect() && reconnectScanInProgress && clientGatt == null) {
                if (matchesReconnectRoom(room)) {
                    reconnectScanInProgress = false;
                    reconnectJoinInProgress = true;
                    connectToRoom(room.roomId, room, false);
                } else if (room.hostPeerId != null && room.hostPeerId.equals(reconnectHostPeerId)
                           && room.sessionId != null && !room.sessionId.equals(reconnectSessionId)) {
                    failReconnect();
                }
                return;
            }

            nativeOnRoomFound(room.roomId, room.sessionId, room.name, room.transport, room.peerCount, room.maxClients, room.rssi);
        }

        @Override
        public void onBatchScanResults(List<ScanResult> results) {
            int count = results != null ? results.size() : 0;
            scanResultCount += count;
            bleLog("scan batch count=" + count + " callbacks=" + scanResultCount);

            if (results == null) {
                return;
            }

            for (ScanResult result : results) {
                onScanResult(ScanSettings.CALLBACK_TYPE_ALL_MATCHES, result);
            }
        }

        @Override
        public void onScanFailed(int errorCode) {
            bleLog("scan failed code=" + errorCode);
            if (hasActiveReconnect()) {
                failReconnect();
            } else if (hasActiveMigration()) {
                failMigration();
            } else {
                nativeOnError("scan_failed", "Scan failed with code " + errorCode + ".");
            }
        }
    };

    private final BluetoothGattServerCallback gattServerCallback = new BluetoothGattServerCallback() {
        @Override
        public void onConnectionStateChange(BluetoothDevice device, int status, int newState) {
            if (device == null) {
                return;
            }

            String deviceKey = safeDeviceKey(device);
            bleLog("server connection state: device=" + deviceKey + " status=" + status + " state=" + newState);

            if (newState == BluetoothGatt.STATE_CONNECTED) {
                if (!hosting) {
                    return;
                }

                if (connectedClients.size() + pendingClients.size() + peerReconnectTimeouts.size() >= maxClients) {
                    if (gattServer != null) {
                        gattServer.cancelConnection(device);
                    }
                    return;
                }

                pendingClients.put(deviceKey, device);
                pendingClientTimestamps.put(deviceKey, System.currentTimeMillis());
            } else if (newState == BluetoothGatt.STATE_DISCONNECTED) {
                pendingClients.remove(deviceKey);
                pendingClientTimestamps.remove(deviceKey);
                deviceMtu.remove(deviceKey);
                notificationQueues.remove(deviceKey);

                String peerId = devicePeerIds.remove(deviceKey);
                if (peerId != null) {
                    connectedClients.remove(peerId);

                    if (hosting && !migrationDepartureInProgress) {
                        beginPeerReconnectGrace(peerId);
                        startAdvertising();
                    } else {
                        removeSessionPeer(peerId);
                        rosterStatus.remove(peerId);
                    }
                }
            }
        }

        @Override
        public void onMtuChanged(BluetoothDevice device, int mtu) {
            if (device == null) {
                return;
            }

            bleLog("server mtu changed: device=" + safeDeviceKey(device) + " mtu=" + mtu);
            deviceMtu.put(safeDeviceKey(device), Math.max(DEFAULT_ATT_MTU, mtu));
        }

        @Override
        public void onNotificationSent(BluetoothDevice device, int status) {
            if (device == null) {
                return;
            }

            String deviceKey = safeDeviceKey(device);
            ArrayDeque<byte[]> queue = notificationQueues.get(deviceKey);
            if (queue == null || queue.isEmpty()) {
                return;
            }

            if (status != BluetoothGatt.GATT_SUCCESS) {
                notificationQueues.remove(deviceKey);
                nativeOnError("send_failed", "BLE notification delivery failed.");
                return;
            }

            queue.removeFirst();
            if (queue.isEmpty()) {
                notificationQueues.remove(deviceKey);
            } else {
                pumpNotificationQueue(device);
            }
        }

        @Override
        public void onServiceAdded(int status, BluetoothGattService service) {
            if (service == null || !SERVICE_UUID.equals(service.getUuid())) {
                return;
            }

            if (!hosting || gattServer == null) {
                return;
            }

            if (status != BluetoothGatt.GATT_SUCCESS) {
                leaveHostOnly();
                hosting = false;
                if (hasActiveMigration() && migration.becomingHost) {
                    failMigration();
                } else {
                    nativeOnError("host_failed", "Bluetooth GATT service registration failed.");
                }
                return;
            }

            hostServiceReady = true;
            if (!startAdvertising()) {
                leaveHostOnly();
                hosting = false;
                if (hasActiveMigration() && migration.becomingHost) {
                    failMigration();
                }
            }
        }

        @Override
        public void onDescriptorReadRequest(BluetoothDevice device, int requestId, int offset, BluetoothGattDescriptor descriptor) {
            if (gattServer == null) {
                return;
            }

            bleLog("descriptor read: device=" + safeDeviceKey(device) + " uuid=" + (descriptor != null ? descriptor.getUuid() : null));
            if (descriptor == null || !CLIENT_CONFIG_UUID.equals(descriptor.getUuid())) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_FAILURE, offset, null);
                return;
            }

            byte[] value = descriptor.getValue();
            if (value == null) {
                value = BluetoothGattDescriptor.DISABLE_NOTIFICATION_VALUE;
            }

            gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, offset, value);
        }

        @Override
        public void onDescriptorWriteRequest(BluetoothDevice device, int requestId, BluetoothGattDescriptor descriptor, boolean preparedWrite, boolean responseNeeded, int offset, byte[] value) {
            bleLog("descriptor write: device=" + safeDeviceKey(device)
                + " uuid=" + (descriptor != null ? descriptor.getUuid() : null)
                + " len=" + (value != null ? value.length : 0)
                + " hex=" + hexPreview(value));
            if (descriptor == null || !CLIENT_CONFIG_UUID.equals(descriptor.getUuid())) {
                if (responseNeeded && gattServer != null) {
                    gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_FAILURE, offset, null);
                }
                return;
            }

            descriptor.setValue(value != null ? value : BluetoothGattDescriptor.DISABLE_NOTIFICATION_VALUE);

            if (responseNeeded && gattServer != null) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, offset, descriptor.getValue());
            }
        }

        @Override
        public void onCharacteristicReadRequest(BluetoothDevice device, int requestId, int offset, BluetoothGattCharacteristic characteristic) {
            if (gattServer == null) {
                return;
            }

            bleLog("characteristic read: device=" + safeDeviceKey(device)
                + " uuid=" + (characteristic != null ? characteristic.getUuid() : null)
                + " offset=" + offset);
            if (characteristic == null || !MESSAGE_UUID.equals(characteristic.getUuid())) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_FAILURE, offset, null);
                return;
            }

            byte[] value = characteristic.getValue();
            if (value == null) {
                value = new byte[0];
            }

            gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, offset, value);
        }

        @Override
        public void onCharacteristicWriteRequest(BluetoothDevice device, int requestId, BluetoothGattCharacteristic characteristic, boolean preparedWrite, boolean responseNeeded, int offset, byte[] value) {
            if (responseNeeded && gattServer != null) {
                gattServer.sendResponse(device, requestId, BluetoothGatt.GATT_SUCCESS, offset, null);
            }

            if (value == null || device == null) {
                return;
            }

            String deviceKey = safeDeviceKey(device);
            bleLog("characteristic write: device=" + deviceKey
                + " uuid=" + (characteristic != null ? characteristic.getUuid() : null)
                + " len=" + value.length
                + " hex=" + hexPreview(value));
            ReassembledPacket reassembled = processIncomingFragment(deviceKey, value);
            if (reassembled == null) {
                return;
            }

            Packet packet = decodePacket(reassembled.data);
            if (packet == null) {
                return;
            }

            if (!validateInboundPacketFromDevice(packet, deviceKey)) {
                return;
            }

            bleLog("host received packet device=" + deviceKey + " " + packetSummary(packet));

            if (PACKET_KIND_DATA.equals(packet.kind) && isDuplicateMessage(packet.fromPeerId, packet.msgType, packet.messageId)) {
                return;
            }

            if (PACKET_KIND_CONTROL.equals(packet.kind)) {
                metricCtrlIn++;
                if (CONTROL_HELLO.equals(packet.msgType)) {
                    handleHelloFromClient(device, deviceKey, packet);
                } else if (CONTROL_ROSTER_REQUEST.equals(packet.msgType)) {
                    handleRosterRequestFromClient(device, packet);
                }
                return;
            }

            if (!PACKET_KIND_DATA.equals(packet.kind) || packet.fromPeerId.isEmpty()) {
                return;
            }

            if (packet.toPeerId.isEmpty()) {
                // Deliver to self only if sender is not the host
                if (!packet.fromPeerId.equals(localPeerId)) {
                    metricMsgIn++;
                    nativeOnMessage(packet.fromPeerId, packet.msgType, packet.payload);
                }
                notifyClients(reassembled.data, packet.fromPeerId);
            } else if (packet.toPeerId.equals(localPeerId)) {
                metricMsgIn++;
                nativeOnMessage(packet.fromPeerId, packet.msgType, packet.payload);
            } else {
                BluetoothDevice target = connectedClients.get(packet.toPeerId);
                if (target != null) {
                    notifyClient(target, reassembled.data);
                }
            }
        }
    };

    private final BluetoothGattCallback clientGattCallback = new BluetoothGattCallback() {
        @Override
        public void onConnectionStateChange(BluetoothGatt gatt, int status, int newState) {
            bleLog("client connection state: device=" + (gatt != null ? safeDeviceKey(gatt.getDevice()) : "")
                + " status=" + status
                + " state=" + newState);

            if (newState == BluetoothGatt.STATE_CONNECTED) {
                if (!isActiveClientGatt(gatt, "client connection state", true)) {
                    return;
                }
                clientMtu = DEFAULT_ATT_MTU;

                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.LOLLIPOP) {
                    try {
                        if (gatt.requestMtu(DESIRED_ATT_MTU)) {
                            return;
                        }
                    } catch (SecurityException e) {
                        nativeOnError("join_failed", "Bluetooth permission was lost.");
                    }
                }

                gatt.discoverServices();
            } else if (newState == BluetoothGatt.STATE_DISCONNECTED) {
                boolean isActive = (gatt != null && gatt == clientGatt);
                if (!isActive && gatt != null) {
                    gatt.close();
                }

                boolean wasJoined = clientJoined;
                boolean shouldEmit = !clientLeaving && isActive;
                leaveClientOnly();

                // If GATT connect failed during an active reconnect, retry via handleJoinFailure
                if (!shouldEmit && (reconnectJoinInProgress || hasActiveReconnect())) {
                    bleLog("reconnect GATT connect failed status=" + status + ", retrying scan");
                    handleJoinFailure("BLE reconnect connection failed (status=" + status + ").");
                    return;
                }

                if (hasActiveMigration()) {
                    beginMigrationReconnect();
                } else if (shouldEmit && wasJoined && beginUnexpectedHostRecovery()) {
                    return;
                } else if (shouldEmit && wasJoined && beginClientReconnect()) {
                    return;
                } else if (shouldEmit) {
                    finishLeave(null);
                    if (wasJoined) {
                        nativeOnSessionEnded("host_lost");
                    } else {
                        nativeOnError("join_failed", "BLE connection was lost before session join completed.");
                    }
                }
            }
        }

        @Override
        public void onMtuChanged(BluetoothGatt gatt, int mtu, int status) {
            bleLog("client mtu changed: device=" + (gatt != null ? safeDeviceKey(gatt.getDevice()) : "")
                + " mtu=" + mtu
                + " status=" + status);
            if (!isActiveClientGatt(gatt, "client mtu changed", false)) {
                return;
            }
            if (status == BluetoothGatt.GATT_SUCCESS && mtu > 0) {
                clientMtu = Math.max(DEFAULT_ATT_MTU, mtu);
            }

            gatt.discoverServices();
        }

        @Override
        public void onServicesDiscovered(BluetoothGatt gatt, int status) {
            bleLog("client services discovered: device=" + (gatt != null ? safeDeviceKey(gatt.getDevice()) : "")
                + " status=" + status);
            if (!isActiveClientGatt(gatt, "client services discovered", false)) {
                return;
            }
            if (status != BluetoothGatt.GATT_SUCCESS) {
                handleJoinFailure("BLE service discovery failed.");
                return;
            }

            BluetoothGattService service = gatt.getService(SERVICE_UUID);
            if (service == null) {
                handleJoinFailure("BLE service not found on host.");
                return;
            }

            clientMessageCharacteristic = service.getCharacteristic(MESSAGE_UUID);
            if (clientMessageCharacteristic == null) {
                handleJoinFailure("BLE message characteristic not found.");
                return;
            }

            bleLog("client characteristic ready: uuid=" + clientMessageCharacteristic.getUuid());

            gatt.setCharacteristicNotification(clientMessageCharacteristic, true);

            BluetoothGattDescriptor descriptor = clientMessageCharacteristic.getDescriptor(CLIENT_CONFIG_UUID);
            if (descriptor != null) {
                descriptor.setValue(BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE);
                if (!gatt.writeDescriptor(descriptor)) {
                    handleJoinFailure("Could not enable BLE notifications.");
                }
            } else {
                completeLocalJoin();
            }
        }

        @Override
        public void onDescriptorWrite(BluetoothGatt gatt, BluetoothGattDescriptor descriptor, int status) {
            bleLog("client descriptor write: device=" + (gatt != null ? safeDeviceKey(gatt.getDevice()) : "")
                + " uuid=" + (descriptor != null ? descriptor.getUuid() : null)
                + " status=" + status
                + " value=" + (descriptor != null ? hexPreview(descriptor.getValue()) : "<none>"));
            if (!isActiveClientGatt(gatt, "client descriptor write", false)) {
                return;
            }
            if (status != BluetoothGatt.GATT_SUCCESS) {
                handleJoinFailure("Could not enable BLE notifications.");
                return;
            }

            completeLocalJoin();
        }

        @Override
        public void onCharacteristicChanged(BluetoothGatt gatt, BluetoothGattCharacteristic characteristic, byte[] value) {
            if (!isActiveClientGatt(gatt, "client characteristic changed", false)) {
                return;
            }
            handleIncomingPacket(value);
        }

        @Override
        public void onCharacteristicChanged(BluetoothGatt gatt, BluetoothGattCharacteristic characteristic) {
            if (!isActiveClientGatt(gatt, "client characteristic changed", false)) {
                return;
            }
            byte[] value = characteristic.getValue();
            handleIncomingPacket(value);
        }

        @Override
        public void onCharacteristicWrite(BluetoothGatt gatt, BluetoothGattCharacteristic characteristic, int status) {
            if (clientGatt != gatt) {
                return;
            }

            if (!clientWriteQueue.isEmpty()) {
                clientWriteQueue.removeFirst();
            }

            clientWriteInFlight = false;

            if (status != BluetoothGatt.GATT_SUCCESS) {
                metricWriteFail++;
                clientWriteQueue.clear();
                nativeOnError("write_failed", "BLE write to host failed.");
                return;
            }

            pumpClientWriteQueue();
        }

        private void handleIncomingPacket(byte[] value) {
            ReassembledPacket reassembled = processIncomingFragment("host", value);
            if (reassembled == null) {
                return;
            }

            Packet packet = decodePacket(reassembled.data);
            if (packet == null) {
                return;
            }

            if (!validateInboundPacketFromHost(packet)) {
                return;
            }

            bleLog("client received packet " + packetSummary(packet));

            if (PACKET_KIND_CONTROL.equals(packet.kind)) {
                metricCtrlIn++;
                if (!packet.toPeerId.isEmpty() && !packet.toPeerId.equals(localPeerId)) {
                    return;
                }

                if (CONTROL_HELLO_ACK.equals(packet.msgType)) {
                    clientPendingHelloAck = false;
                    clientJoined = true;
                    if (reconnectJoinInProgress && hasActiveReconnect()) {
                        completeReconnectResume();
                    } else if (migrationJoinInProgress && hasActiveMigration()) {
                        completeMigrationResume();
                    } else {
                        nativeOnJoined(joinedSessionId, joinedRoomId, localPeerId, hostPeerId, transport);
                    }
                } else if (CONTROL_JOIN_REJECTED.equals(packet.msgType)) {
                    String reason = decodeControlPayload(packet.payload);
                    clientPendingHelloAck = false;
                    bleLog("join rejected reason=" + reason);
                    String savedRoomId = joinedRoomId;
                    clientLeaving = true;
                    leaveClientOnly();
                    nativeOnJoinFailed(reason, savedRoomId);
                } else if (CONTROL_ROSTER_SNAPSHOT.equals(packet.msgType)) {
                    handleRosterSnapshot(packet.payload);
                } else if (CONTROL_PEER_JOINED.equals(packet.msgType) && !packet.fromPeerId.isEmpty() && !packet.fromPeerId.equals(localPeerId)) {
                    addSessionPeer(packet.fromPeerId);
                    nativeOnPeerJoined(packet.fromPeerId);
                } else if (CONTROL_PEER_LEFT.equals(packet.msgType) && !packet.fromPeerId.isEmpty()) {
                    removeSessionPeer(packet.fromPeerId);
                    nativeOnPeerLeft(packet.fromPeerId, decodeControlPayload(packet.payload));
                } else if (CONTROL_SESSION_MIGRATING.equals(packet.msgType)) {
                    clientWriteQueue.clear();
                    inboundAssemblies.clear();
                    startMigration(decodeMigrationPayload(packet.fromPeerId, packet.payload));
                } else if (CONTROL_SESSION_ENDED.equals(packet.msgType)) {
                    finishLeave(null);
                    nativeOnSessionEnded(decodeControlPayload(packet.payload));
                } else if (CONTROL_HEARTBEAT.equals(packet.msgType)) {
                    handleHeartbeatFingerprint(packet.payload);
                }
                return;
            }

            if (!PACKET_KIND_DATA.equals(packet.kind)) {
                return;
            }

            if (isDuplicateMessage(packet.fromPeerId, packet.msgType, packet.messageId)) {
                return;
            }

            if (packet.toPeerId.isEmpty() || packet.toPeerId.equals(localPeerId)) {
                metricMsgIn++;
                nativeOnMessage(packet.fromPeerId, packet.msgType, packet.payload);
            }
        }
    };
}

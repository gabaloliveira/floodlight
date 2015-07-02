package net.floodlightcontroller.mobility;

/**
 * 
 * 
 * 
 * 
 * 
 * 
 * @author gabrieloliveira
 */

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.net.InetSocketAddress;
import java.net.URL;
import java.net.URLConnection;
import java.security.NoSuchAlgorithmException;
import java.security.spec.InvalidKeySpecException;
import java.security.InvalidKeyException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.SignatureException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.json.JSONArray;
import org.json.JSONObject;

import edu.umass.cs.gns.client.GuidEntry;
import edu.umass.cs.gns.client.UniversalTcpClientExtended;
import edu.umass.cs.gns.client.util.GuidUtils;
import edu.umass.cs.gns.client.util.KeyPairUtils;
import edu.umass.cs.gns.exceptions.GnsException;

import org.projectfloodlight.openflow.protocol.OFFactories;
import org.projectfloodlight.openflow.protocol.OFFactory;
import org.projectfloodlight.openflow.protocol.OFFlowDelete;
import org.projectfloodlight.openflow.protocol.OFFlowMod;
import org.projectfloodlight.openflow.protocol.OFFlowStatsEntry;
import org.projectfloodlight.openflow.protocol.OFFlowStatsReply;
import org.projectfloodlight.openflow.protocol.OFFlowStatsRequest;
import org.projectfloodlight.openflow.protocol.OFMatchV1;
import org.projectfloodlight.openflow.protocol.OFMessage;
import org.projectfloodlight.openflow.protocol.OFPacketIn;
import org.projectfloodlight.openflow.protocol.OFType;
import org.projectfloodlight.openflow.protocol.OFVersion;
import org.projectfloodlight.openflow.protocol.match.MatchField;
import org.projectfloodlight.openflow.protocol.match.Match;
import org.projectfloodlight.openflow.types.DatapathId;
import org.projectfloodlight.openflow.types.IPv4Address;
import org.projectfloodlight.openflow.types.MacAddress;
import org.projectfloodlight.openflow.types.OFBufferId;
import org.projectfloodlight.openflow.types.OFPort;
import org.projectfloodlight.openflow.types.TableId;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import net.floodlightcontroller.core.FloodlightContext;
import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFMessageListener;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.internal.IOFSwitchService;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;
import net.floodlightcontroller.devicemanager.IDevice;
import net.floodlightcontroller.devicemanager.IDeviceListener;
import net.floodlightcontroller.devicemanager.IDeviceService;
import net.floodlightcontroller.devicemanager.SwitchPort;
import net.floodlightcontroller.flowcache.PortDownReconciliation;
import net.floodlightcontroller.linkdiscovery.ILinkDiscoveryListener;
import net.floodlightcontroller.linkdiscovery.ILinkDiscoveryService;
import net.floodlightcontroller.packet.Ethernet;
import net.floodlightcontroller.packet.IPv4;

public class AuspiceListener implements IOFMessageListener, IFloodlightModule, ILinkDiscoveryListener {

	// Our dependencies
	protected IFloodlightProviderService floodlightProvider;
	protected ILinkDiscoveryService linkDiscoveryService;
	protected IDeviceService deviceService;
	protected IOFSwitchService switchService;
	
	//GNS Objects
	UniversalTcpClientExtended client;
	InetSocketAddress address;
    GuidEntry accountGuid;
	
    // Match Factory
    OFFactory myFactory;
	
	// Device Listener impl class
	protected DeviceListenerImpl deviceListener;

	// Logger object
	protected static Logger logger;
	// Lock for Link Up
	protected Boolean isLinkUp;
	protected Boolean isLinkListUp;
	// The update that triggered LinkDiscovery
	protected LDUpdate update; 
	protected List<LDUpdate> updateList;
	//GNS IP
	private static final String GNSIP = "192.168.0.15";
	//GNS Port
	private static final int GNSPORT = 24398;
	// The controller IP
	private static final String FLOODLIGHTIP = "localhost";
	// List of MAC Addresses known to this controller and where it is/was located
	protected Map<MacAddress, DatapathId> macsToSwitch;
	// List of MAC Addresses known to this controller and to which port it is/was connected
	protected Map<MacAddress, OFPort> macsToPort;
	// List of MAC Addresses known to this controller and its IP Address
	protected Map<MacAddress, IPv4Address> macsToIp;
	// Mapping of 2 MAC Addresses that already had a flow between then (so they contacted before) 
	protected Map<MacAddress, MacAddress> ongoingConnections;
	// Mapping of DPID to IOFSwitch
	protected Map<DatapathId, IOFSwitch> switchMap;
	// List of MAC Addresses that suffered a Link Down
	protected Set<MacAddress> downedMacs;
	// List of MAC Addresses that had its location changed (i.e. just moved)
	protected Set<MacAddress> movedMacs;
	// List of MAC Addresses that had its IP changed 
	protected Set<MacAddress> changedIPMacs;
	//number used to identify flow-mods
	private int flowNumber = 0;
	// GNS account email
	private static final String ACCOUNTID = "gabrieloliveira@bcc.ic.uff.br";
	// Location of GNS Private Key File
	private static final String PRIVATEKEYFILE = "/Users/gabrieloliveira/.ssh/auspice.key";
	
	public Set<MacAddress> getDownedMacs(){
		return downedMacs;
	}
	
	public Set<MacAddress> getMovedMacs(){
		return movedMacs;
	}
	
	// IFloodlightModule implementation
	@Override
	public String getName() {
		return AuspiceListener.class.getSimpleName();
	}
	
	private void getCurrentFlows(IOFSwitch mySwitch, MacAddress mac){
		// Get current flows
		List<OFFlowStatsReply> statsReply = new ArrayList<OFFlowStatsReply>();
	    List<OFFlowStatsReply> values = null;
	    Future<List<OFFlowStatsReply>> future;
	       
		// Statistics request object for getting flows
		OFFlowStatsRequest req = mySwitch.getOFFactory().buildFlowStatsRequest()
						.setMatch(mySwitch.getOFFactory().buildMatch().build())
		        		.setOutPort(macsToPort.get(mac))
		        		.setTableId(TableId.ALL)
		        		.build();

		try {
			future = mySwitch.writeStatsRequest(req);
		    values = future.get(10, TimeUnit.SECONDS);
		    if (values != null) {
		    	for (OFFlowStatsReply stat : values) {
		    		statsReply.add(stat);
		        }
		    }
		} catch (Exception e) {
			logger.error("Failure retrieving statistics from switch " + mySwitch, e);
		}
		if (!statsReply.isEmpty()){
			for (OFFlowStatsReply flow : statsReply){
				for (OFFlowStatsEntry flowEntry : flow.getEntries()){
					if (flowEntry.getMatch().get(MatchField.ETH_DST).equals(mac)){
						System.out.println("[RemoveFlows] Found a flow from "
										+ flowEntry.getMatch().get(MatchField.ETH_SRC).toString()
		        						+ " to "
		        						+ flowEntry.getMatch().get(MatchField.ETH_DST).toString()
		        						+".");
		        		System.out.println("[GetCurrentFlows] Adding to ongoingConnections: from "
		        						+ flowEntry.getMatch().get(MatchField.ETH_SRC) 
		        						+ " to "
		        						+ flowEntry.getMatch().get(MatchField.ETH_DST));
		        									
		        		ongoingConnections.put(flowEntry.getMatch().get(MatchField.ETH_DST), flowEntry.getMatch().get(MatchField.ETH_SRC));
		  			}
	      		}
			}
		}		
	}
	private void removeFlows(IOFSwitch mySwitch, MacAddress mac){
		Match match = myFactory.buildMatch()
				.setExact(MatchField.ETH_DST, mac)
				.build();
		OFFlowDelete flowDelete = myFactory.buildFlowDelete()
				.setBufferId(OFBufferId.NO_BUFFER)
				.setMatch(match)
				.build();
		try{
			mySwitch.write(flowDelete);
			mySwitch.flush();
			System.out.println("[RemoveFlows] Sent flowmod Delete command");
		} catch (Exception e) {
			logger.error("tried to write flow_mod delete to {} but failed: {}", 
					mySwitch.getId(), e.getMessage());
		}
	}

	private void auspiceInitialize() throws UnsupportedEncodingException, 
										IOException, GnsException, InvalidKeySpecException, 
										NoSuchAlgorithmException{
		//Select Server
		address = new InetSocketAddress(GNSIP, GNSPORT);
	    
		
		// Create a new client object
		client	= new UniversalTcpClientExtended(
												address.getHostName(), address.getPort());
	
	    // Retrive the GUID using the account id
	    String guid = client.lookupGuid(ACCOUNTID);   
	    // Get the public key from the GNRS
	    PublicKey publicKey = client.publicKeyLookupFromGuid(guid);
	    // Load the private key from a file
	    PrivateKey privateKey = KeyPairUtils.getPrivateKeyFromPKCS8File(PRIVATEKEYFILE);
	    // Create a GuidEntry object
	    accountGuid = new GuidEntry(ACCOUNTID, guid, publicKey, privateKey);
	}

	private void auspiceUpdateLocation (MacAddress mac, DatapathId dpid, OFPort port) throws IOException, 
	InvalidKeySpecException, NoSuchAlgorithmException, GnsException,
	InvalidKeyException, SignatureException, Exception {
		
	
	    // Add or lookup MAC Address as a new GUID Entry
	    GuidEntry macGuid = GuidUtils.lookupOrCreateGuid(client, accountGuid, mac.toString());
	    
	    // Use the GuidEntry create or update Switch and port in the GNS
	    System.out.println("[auspiceUpdateLocation] Setting location of "+ mac
	    					+" as switch "+ dpid
	    					+" port number "+ port);
	    client.fieldReplaceOrCreate(macGuid.getGuid(), "switch", dpid.toString(), accountGuid);
	    client.fieldReplaceOrCreate(macGuid.getGuid(), "port", port.toString(), accountGuid);

	}
	
	private void auspiceRemoveEntry (MacAddress mac) throws IOException, 
	InvalidKeySpecException, NoSuchAlgorithmException, GnsException,
	InvalidKeyException, SignatureException, Exception {
		
	
	    // Add or lookup MAC Address as a new GUID Entry
	    GuidEntry macGuid = GuidUtils.lookupOrCreateGuid(client, accountGuid, mac.toString());
	    
	    // Use the GuidEntry to delete this entry
	    client.guidRemove(accountGuid, macGuid.getGuid());
			
	}
	
	private void auspiceUpdateIp (GuidEntry macGuid, MacAddress mac, JSONArray ips) throws IOException, 
	InvalidKeySpecException, NoSuchAlgorithmException, GnsException,
	InvalidKeyException, SignatureException, Exception {
		
		if (ips.length()==0) return;
		// remove all IPs associated to it in Auspice
	    //client.fieldClear(macGuid.getGuid(), "IPs", accountGuid);
	    // Use the GuidEntry create or update IP record in the GNS
	    client.fieldReplaceOrCreateList(macGuid.getGuid(), "IPs", ips, accountGuid);
	}
	
	
	private void flowUpdate(DatapathId SourceSw, String DstSw, IPv4Address sourceIp, IPv4Address oldIpv4, 
							String newIpv4,	OFPort oldPort, String newPort){
		
		
		// Flow attributes
		String sourceDpid = SourceSw.toString();
		String dstDpid = DstSw;
		String name = "flow-mod-"+ ++flowNumber;
		//String name = "flow-mod-1";
		String etherType = "0x800"; // IPv4
		
		String ipv4Src = sourceIp.toString();
		String oldIpv4Dst = oldIpv4.toString();
		String newIpv4Dst = newIpv4;
		String outputSrc = oldPort.toString();
		String outputDst = newPort;
		
	
		String flowIda = "{\"switch\": \"" + sourceDpid
				+ "\", \"name\":\"" + name
				+ "\", \"cookie\":\"0"
				+ "\", \"priority\":\"32768" 
				+ "\",\"active\":\"true"
				+ "\",\"eth_type\":\"" + etherType
				+ "\",\"ipv4_dst\":\"" + oldIpv4Dst
				+ "\", \"actions\":\"set_ipv4_dst=" + newIpv4Dst
				+ ",output=" + outputDst
				+ "\"}";
		String flowVolta = "{\"switch\": \"" + dstDpid
				+ "\", \"name\":\"flow-mod-2" 
				+ "\", \"cookie\":\"0"
				+ "\", \"priority\":\"32768"
				+ "\",\"active\":\"true"
				+ "\",\"eth_type\":\"" + etherType
				+ "\",\"ipv4_src\":\"" + newIpv4Dst
				+ "\", \"ipv4_dst\":\"" + ipv4Src
				+ "\", \"actions\":\"set_ipv4_src=" + oldIpv4Dst
				+ ",output=" + outputSrc 
				+ "\"}";
		String jsonResponse = "";
		URL url;
		
		System.out.println("[FlowUpdate]" + flowIda);
		System.out.println("[FlowUpdate]" + flowVolta);
		try {
			
			flowNumber++;
			// Establish Connection
			url = new URL("http://" + FLOODLIGHTIP + ":8080/wm/staticflowpusher/json");
			URLConnection conn = url.openConnection();
			conn.setDoOutput(true);
			
			// Send the "ping" flow
			OutputStreamWriter wr = new OutputStreamWriter(conn.getOutputStream());
			wr.write(flowIda);
			wr.flush();
	
			// Get the response
			BufferedReader rd = new BufferedReader(new InputStreamReader(
					conn.getInputStream()));
			String line;
			while ((line = rd.readLine()) != null) {
				jsonResponse = jsonResponse.concat(line);
			}
			wr.close();
			rd.close();
			
			
			// Parse the response
			JSONObject json = new JSONObject(jsonResponse);
			
			System.out.println("[FlowUpdate]" + json.getString("status"));
			
			
			// Send the "pong" flow
			conn = url.openConnection();
			conn.setDoOutput(true);
			wr = new OutputStreamWriter(conn.getOutputStream());
			wr.write(flowVolta);
			wr.flush();
	
			// Get the response
			rd = new BufferedReader(new InputStreamReader(
					conn.getInputStream()));
			line = "";
			while ((line = rd.readLine()) != null) {
				jsonResponse = jsonResponse.concat(line);
			}
			wr.close();
			rd.close();
			
			
			// Parse the response
			json = new JSONObject(jsonResponse);
			
			System.out.println("[FlowUpdate]" + json.getString("status"));
	
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	@Override
		public net.floodlightcontroller.core.IListener.Command receive(
				IOFSwitch sw, OFMessage msg, FloodlightContext cntx) {
			
			Ethernet eth =
		                IFloodlightProviderService.bcStore.get(cntx,
		                                            IFloodlightProviderService.CONTEXT_PI_PAYLOAD);
			IPv4 ipv4 = null;
		        if(eth.getPayload() instanceof IPv4)
		        	ipv4 = (IPv4) eth.getPayload();
			 
		        MacAddress sourceMAC = eth.getSourceMACAddress();
		        MacAddress dstMAC = eth.getDestinationMACAddress();
	            // Now to find to which port it is connected		        
				OFPort inPort = (((OFPacketIn)msg).getVersion().compareTo(OFVersion.OF_12) < 0 ? 
								((OFPacketIn)msg).getInPort() : 
								((OFPacketIn)msg).getMatch().get(MatchField.IN_PORT));

			//System.out.println("[RECEIVE] Received a packet! from "+sourceMAC+" to "+dstMAC);
				
			// if it is downed currently we drop it
			if (downedMacs.contains(dstMAC)){
				System.out.println("[RECEIVE] This packet is going to a downed mac!");
			}
		    // if it has moved, we generate the flows for this particular destinaton
			if (ongoingConnections.containsKey(dstMAC))
				if (ongoingConnections.get(sourceMAC).equals(dstMAC))
					System.out.println("[RECEIVE] There was an ongoing connection between "+ dstMAC+" and "+sourceMAC);

			//if its IP has changed and there was a previous connection before link down
			if ((changedIPMacs.contains(dstMAC)) 
					&& (ipv4 != null)
					&& (ongoingConnections.containsKey(dstMAC))
					&& (ongoingConnections.get(dstMAC).equals(sourceMAC))){
					
				System.out.println("[RECEIVE] Changed IP address!!");
				removeFlows(sw, dstMAC);
				String newIpv4;
				String newSw;
				String newPort;
				// Create a guid Entry object
				GuidEntry macGuid;
				try {
					macGuid = GuidUtils.lookupOrCreateGuid(client, accountGuid, dstMAC.toString());
					// get one of its IPs
					newIpv4 = client.fieldReadArrayFirstElement(macGuid, "IPs");
					// get its switch
					newSw = client.fieldReadArrayFirstElement(macGuid, "switch");
					// get its port
					newPort = client.fieldReadArrayFirstElement(macGuid, "port");
					flowUpdate(sw.getId(), newSw, ipv4.getSourceAddress(), ipv4.getDestinationAddress(), 
									newIpv4, inPort , newPort);
				} catch (Exception e) {
					e.printStackTrace();
				}
				//System.out.println("[RECEIVE] Removing from ongoingConnections:"+dstMAC);
				//ongoingConnections.remove(dstMAC);
				//changedIPMacs.remove(dstMAC);
			}
			//if it has changed location
			if ((movedMacs.contains(dstMAC)) && 
					(ongoingConnections.containsKey(dstMAC)) &&
					(ongoingConnections.get(dstMAC).equals(sourceMAC))){
				
			}

	        // Add MacAddress to our "known nodes" Mapping.
			if (!macsToSwitch.containsKey(sourceMAC)) {
		        	
				/*
		        * If it is not in the Mapping, we insert it. 
		        * If it is in the mapping, we update its entry.
		        */
		        	
		        macsToSwitch.put(sourceMAC, sw.getId());
			}else macsToSwitch.replace(sourceMAC, sw.getId());
		      
			if (!macsToPort.containsKey(sourceMAC)) {
		        	
				/*
		         * If it is not in the Mapping, we insert it. 
		         * If it is in the mapping, we update its entry.
		         */
		        	
				macsToPort.put(sourceMAC, inPort);
			}else macsToPort.replace(sourceMAC, inPort);
				
			if (ipv4 != null) {
				if (!macsToIp.containsKey(sourceMAC)) {
		        	
					/*
					 * If it is not in the Mapping, we insert it. 
					 * If it is in the mapping, we update its entry.
					 */
		        	
					macsToIp.put(sourceMAC, ipv4.getSourceAddress());
					System.out.println("[RECEIVE] Added IP "
										+ ipv4.getSourceAddress().toString()
										+ " to MAC map " + sourceMAC.toString());
				}else {
					if (!macsToIp.get(sourceMAC).equals(ipv4.getSourceAddress())){
						macsToIp.replace(sourceMAC, ipv4.getSourceAddress());
						System.out.println("[RECEIVE] Added IP "
											+ ipv4.getSourceAddress().toString()
											+ " to MAC map " + sourceMAC.toString());
					}
				}
			}
	
			return Command.CONTINUE;
		}

	@Override
		public void linkDiscoveryUpdate(LDUpdate update) {
			MacAddress mac = null;
			//OFPort oldPort = null;
			switch (update.getOperation()){
				case PORT_DOWN:
					isLinkUp=false;
					if (macsToSwitch.containsValue(update.getSrc())){
						for (Map.Entry<MacAddress, DatapathId> entry : macsToSwitch.entrySet()){
							if (entry.getValue().equals(update.getSrc())){
								/*
								 *  We found one MAC Address which is/was connected to the switch.
								 *  Now we need to check the port this mac was connected to.
								 *  As there's only one MAC-switch-port combination, we now are sure
								 *  we found the MAC that suffered link update.
								 */
								if ((macsToPort.containsKey(entry.getKey())) && 
										(macsToPort.get(entry.getKey()).equals(update.getSrcPort()))){
									/*
									 * If there's a mac in the mac-port Map, and it's value is the same as 
									 * the port that triggered the update, we now know the MAC that was
									 * updated
									 */
									mac = entry.getKey();
								}
							} if (mac == null) break; 
						} if (mac == null) logger.warn("Couldn't find which node got offline.");
						//
						System.out.println("[PORT_DOWN] Clearing ongoingConnections");
						ongoingConnections.clear();
						DatapathId dpid = macsToSwitch.get(mac);
						IOFSwitch mySwitch =  switchService.getSwitch(dpid);
						// Check if there was any flows to this host (active flow=active connection) 
						getCurrentFlows(mySwitch, mac);
						// Remove all flows related to this MAC
						removeFlows(mySwitch, mac);
						System.out.println("[PORT_DOWN]Adding to downedMacs "+mac);
						downedMacs.add(mac);	
						try {
							auspiceRemoveEntry(mac);
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
					break;
				case PORT_UP:
					// DeviceManager will find port and Switch info
					isLinkUp=true;
					break;
				default:
					//ignore
			}
			
		}

	@Override
	public void linkDiscoveryUpdate(List<LDUpdate> updateList) {
		// Tratar os updates separadamente
		for( LDUpdate update : updateList){
			this.linkDiscoveryUpdate(update);
		}
		this.updateList = updateList;
		isLinkListUp = true;
		
	}

	@Override
	public void startUp(FloodlightModuleContext context)
			throws FloodlightModuleException {
		 floodlightProvider.addOFMessageListener(OFType.PACKET_IN, this);
		 linkDiscoveryService.addListener(this);
		 deviceService.addListener(this.deviceListener);
	}

	@Override
	public void init(FloodlightModuleContext context)
			throws FloodlightModuleException {
		// Initialize our dependencies
		floodlightProvider = context.getServiceImpl(IFloodlightProviderService.class);
		linkDiscoveryService = context.getServiceImpl(ILinkDiscoveryService.class);
		deviceService = context.getServiceImpl(IDeviceService.class);
		switchService = context.getServiceImpl(IOFSwitchService.class);
		
		deviceListener = new DeviceListenerImpl();		
	    myFactory = OFFactories.getFactory(OFVersion.OF_13); /* Get an OpenFlow 1.3 factory. */
	    
		logger = LoggerFactory.getLogger(AuspiceListener.class);
		try {
			auspiceInitialize();
		} catch (InvalidKeySpecException | NoSuchAlgorithmException
				| IOException | GnsException e) {
			e.printStackTrace();
		}
		
		// Our lists
	    macsToSwitch = new HashMap<MacAddress, DatapathId>();
	    macsToPort = new HashMap<MacAddress, OFPort>();
	    macsToIp = new HashMap<MacAddress, IPv4Address>();
	    ongoingConnections = new HashMap<MacAddress, MacAddress>();
	    switchMap = new HashMap<DatapathId, IOFSwitch>();
	    downedMacs = new ConcurrentSkipListSet<MacAddress>();
	    movedMacs = new ConcurrentSkipListSet<MacAddress>();
	    changedIPMacs = new ConcurrentSkipListSet<MacAddress>();
	    
	    //Other vars
	    isLinkUp = false;
	
	}

	@Override
	public boolean isCallbackOrderingPrereq(OFType type, String name) {
		return false;
	}

	@Override
	public boolean isCallbackOrderingPostreq(OFType type, String name) {
		// we need to run before everything, as we are updating flow tables.
		return true;
	}

	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleServices() {
		return null;
	}

	@Override
	public Map<Class<? extends IFloodlightService>, IFloodlightService> getServiceImpls() {
		return null;
	}

	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleDependencies() {
		Collection<Class<? extends IFloodlightService>> l = 
				new ArrayList<Class<? extends IFloodlightService>>();
		l.add(IFloodlightProviderService.class);
		l.add(ILinkDiscoveryService.class);
		l.add(IDeviceService.class);
		return l;
	}

	// IDeviceListener
		class DeviceListenerImpl implements IDeviceListener{
			@Override
			public void deviceAdded(IDevice device) {
				OFPort port = null;
				DatapathId dpid = null;
				// Set up parameters for it in Auspice
				try {
					/* 
					 * Assuming there's only one attachment point at a time, this will work
					 * If there's more than one attachment point, we need to check updateList
					 * and match this switch+port to updateList switch+port combination, so 
					 * we know which switch+port caused the update.
					 *  TODO Handle connection to more than one attachment point at a time.
					 */
					for (SwitchPort attachment : device.getAttachmentPoints()){
						dpid = attachment.getSwitchDPID();
						port = attachment.getPort();
						System.out.println("[DeviceAdded] "+attachment);
						auspiceUpdateLocation(device.getMACAddress(), dpid, port);
					}
					
					
				} catch (Exception e) {
					e.printStackTrace();
				}
			}

			@Override
			public void deviceRemoved(IDevice device) {
				// Ignore, this is only for timeouts.
			}

			@Override
			public void deviceIPV4AddrChanged(IDevice device) {

				List<IPv4Address> ips = Arrays.asList(device.getIPv4Addresses());
					
				JSONArray array = new JSONArray();
				try {
					// Add or lookup MAC Address as a new GUID Entry
					GuidEntry macGuid = GuidUtils.lookupOrCreateGuid(client, accountGuid, device.getMACAddressString());

					for (IPv4Address ip : ips){
						System.out.println("[AddrChanged] new ip: "+ip.toString());
						if (macsToIp.containsKey(device.getMACAddress())){
							System.out.println("[AddrChanged] oldIP: "+macsToIp.get(device.getMACAddress()).toString());
							if ((!ip.toString().equals("0.0.0.0")) && (!macsToIp.get(device.getMACAddress()).equals(ip))){
								System.out.println("[AddrChanged] Colocando IP no array: "+ip.toString());
								changedIPMacs.add(device.getMACAddress());
								array.put(ip.toString());
							}	
						}else{
							System.out.println("[AddrChanged(else)] oldIP: null");
							if (!ip.toString().equals("0.0.0.0")){
								System.out.println("[AddrChanged(else)] Colocando IP no array: "+ip.toString());	
								array.put(ip.toString());
							}
						}	
					}
					if (array.length()!=0)
						auspiceUpdateIp(macGuid, device.getMACAddress(), array);
				}	catch (Exception e) {
					e.printStackTrace();
				}
			}
			
			@Override
			public void deviceMoved(IDevice device) {
				OFPort port = null;
				DatapathId dpid = null;
				// Set up parameters for it in Auspice
				try {
					/* 
					 * Assuming there's only one attachment point at a time, this will work
					 * If there's more than one attachment point, we need to check updateList
					 * and match this switch+port to updateList switch+port combination, so 
					 * we know which switch+port caused the update.
					 *  TODO Handle connection to more than one attachment point at a time.
					 */
					if (isLinkUp){
						// This is a link up event
						for (SwitchPort attachment : device.getAttachmentPoints()){
							dpid = attachment.getSwitchDPID();
							port = attachment.getPort();
							if (macsToSwitch.containsKey(device.getMACAddress())
									&& downedMacs.contains(device.getMACAddress())){
								// Do we know this Mac Address? i.e It has sent/received something before?
								//logger.warn("Device {} is now on switch {} on port number {}",new Object[] {device.getMACAddress(), 
									//		update.getSrc(), update.getSrcPort()});
								System.out.println("[DeviceMoved]Device "+device.getMACAddress()
													+" is now on switch "+dpid
													+" on port number "+ port);
								try {
									auspiceUpdateLocation(device.getMACAddress(), dpid, port);
								} catch (Exception e) {
									e.printStackTrace();
								}
								if( (dpid.equals(macsToSwitch.get(device.getMACAddress()))) 
										&& (port.equals(macsToPort.get(device.getMACAddress())))){
									// Link up event but device location didn't change
									System.out.println("[deviceMoved] Removing from downedMacs: "+device.getMACAddressString());
									downedMacs.remove(device.getMACAddress());
									return;
								}
								System.out.println("[deviceMoved] Removing from downedMacs: "+device.getMACAddressString());
								downedMacs.remove(device.getMACAddress());
								System.out.println("[deviceMoved] Adding to movedMacs: "+device.getMACAddressString());
								movedMacs.add(device.getMACAddress());
							}
						}
					}//else we don't need to do anything, as no one has ever contacted this device
				}catch (Exception e) {
					e.printStackTrace();
				}
				isLinkUp=false;
			}

			@Override
			public void deviceVlanChanged(IDevice device) {
				//ignore
			}

			@Override
			public String getName() {
				return AuspiceListener.this.getName();
			}

			@Override
			public boolean isCallbackOrderingPrereq(String type, String name) {
				return false;
			}

			@Override
			public boolean isCallbackOrderingPostreq(String type, String name) {
				// We need to go before forwarding
				return false;
			}

		}
	
}

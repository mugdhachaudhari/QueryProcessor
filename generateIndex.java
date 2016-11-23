import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.RandomAccessFile;
import java.io.Reader;
import java.io.Writer;
import java.io.ObjectInputStream.GetField;
import java.lang.reflect.Array;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.PriorityQueue;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

class MinHeap {
	private HeapStruct[] heap;
	private int size;
	private int maxSize;
	private static final int FRONT = 1;

	public MinHeap(int maxSize){
	    this.heap = new HeapStruct[maxSize+1];
	    heap[0] = null;
	    this.size = 0;
	}

	private int getParent(int position){
	    return position/2;
	}

	private int getLeftChild(int position){
	    return 2*position;
	}

	private int getRightChild(int position){
	    return 2*position+1;
	}

	private void swap(int position1, int position2){
		HeapStruct temp = heap[position1];
	    heap[position1] = heap[position2];
	    heap[position2] = temp;
	}

	private boolean isLeaf(int position){

	    if(position > size/2){
	        return true;
	    }
	    return false;
	}

	public void insert(HeapStruct data){
	    heap[++size] = data;
	    int currentItem = size;
	    while(size > 1 && getParent(currentItem) != 0 && heap[getParent(currentItem)].compareTo(heap[currentItem]) > 0 ){
	        swap(getParent(currentItem),currentItem);
	        currentItem = getParent(currentItem);
	    }
	}

	public HeapStruct delete(){
		HeapStruct itemPopped = heap[FRONT];
	    heap[FRONT] = heap[size--];
	    heapify(FRONT);
	    return itemPopped;
	}
	
	public HeapStruct getFront() {
		return heap[FRONT];
	}
	
	public int getSize(){
		return size;
	}
	
	public void replaceFront(HeapStruct data) {
		heap[FRONT] = data;
		heapify(FRONT);
	}

	public void heapify(int position){
	    if(isLeaf(position)){
	        return;
	    }
	    if (getRightChild(position) > size) {
	    	if ( (heap[position].compareTo(heap[getLeftChild(position)]) > 0)) {
	    		swap(position, getLeftChild(position));
	    	}
	    } else {
		    if ( (heap[position].compareTo(heap[getLeftChild(position)]) > 0) || (heap[position].compareTo(heap[getRightChild(position)]) > 0)){

		        if(heap[getLeftChild(position)].compareTo(heap[getRightChild(position)]) < 0){
		            swap(position , getLeftChild(position));
		            heapify(getLeftChild(position));
		        }
		        else{
		            swap(position , getRightChild(position));
		            heapify(getRightChild(position));
		        }
		    }
	    }
	}

	@Override
	public String toString(){
	    StringBuilder output = new StringBuilder();
	    for(int i=1; i<= size/2; i++){
	        output.append("Parent :"+ heap[i]);
	        String left = heap[getLeftChild(i)].toString();
	        output.append("LeftChild : "+left + "\n"); 
	        String right = null;
	        if (getRightChild(i) <= size) {
	        	right = heap[getRightChild(i)].toString();
	        	output.append("RightChild :"+ right + "\n");
	        }
	        
	    }
	    return output.toString();
	}
}


class HeapStruct implements Comparable<HeapStruct> {
	public String term;
	public int fileNr;
	public int docFreq, postingPtr;
	public byte[] posting;
	public String postingAscii;
	
	public HeapStruct(String term, int fileNr, int docFreq, int postingPtr, byte[] posting) {
		this.term = term;
		this.fileNr = fileNr;
		this.docFreq = docFreq;
		this.postingPtr = postingPtr;
		this.posting = posting;
	}
	
	public HeapStruct(String term, int fileNr, int docFreq, int postingPtr, String posting) {
		this.term = term;
		this.fileNr = fileNr;
		this.docFreq = docFreq;
		this.postingPtr = postingPtr;
		this.postingAscii = posting;
	}
	
	public int compareTo(HeapStruct obj) {
		if (this.term.compareTo(obj.term) > 0) {
			return 1;
		} else if (this.term.compareTo(obj.term) < 0) {
			return -1;
		} else if (this.fileNr > obj.fileNr) {
			return 1;
		} else {
			return -1;
		}
	}
	
	public String toString() {
		if (generateIndex.mode.equals("ascii")) {
			return(term + " , " + fileNr + " , " + docFreq + " , " + postingPtr + " , " + postingAscii);
		} else {
			return(term + " , " + fileNr + " , " + docFreq + " , " + postingPtr + " , " + Arrays.toString(posting));
		}

	}
}

class ChunkLexiconPartial {
	public String term;
	public int postingNr;
	public int docFreq;
	
	public ChunkLexiconPartial(String term, int postingNr, int docFreq) {
		this.term = term;
		this.postingNr = postingNr;
		this.docFreq = docFreq;
	}
}

class MergeBuffer {
	public BufferedOutputStream bo;
	public BufferedWriter boAscii;
	public BufferedWriter bw;
	public BufferedWriter docUrlbw;
	public String prevTerm;
	public int prevDocFreq;
	public byte[] prevInv;
	public String prevInvAscii;
	public int glbPosition = 0;
	public Integer prevDocId = 0;
	
	public MergeBuffer(BufferedOutputStream bo, BufferedWriter bw, BufferedWriter docUrlbw) {
		this.bo = bo;
		this.bw = bw;
		this.docUrlbw = docUrlbw;
	}
	
	public MergeBuffer(BufferedWriter bo, BufferedWriter bw, BufferedWriter docUrlbw) {
		this.boAscii = bo;
		this.bw = bw;
		this.docUrlbw = docUrlbw;
	}
}

class partialIndexBuffer {
	public BufferedInputStream invIndBStream;
	public BufferedReader invIndBStreamAscii;
	public BufferedReader lexBufReader;
	public String[] prevLex;
	
	public partialIndexBuffer(BufferedInputStream ds, BufferedReader br) {
		invIndBStream = ds;
		lexBufReader = br;
		try {
			String prevLexStr = br.readLine();
			if (prevLexStr != null) {
				prevLex = prevLexStr.trim().split("\t");
			}
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
	}
	
	public partialIndexBuffer(BufferedReader ds, BufferedReader br) {
		invIndBStreamAscii = ds;
		lexBufReader = br;
		try {
			String prevLexStr = br.readLine();
			if (prevLexStr != null) {
				prevLex = prevLexStr.trim().split("\t");
			}
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
	}
}

public class generateIndex {
	private static HashMap<Integer, Integer> fileDocMap;
	private static boolean isDebug = true;
	private static int maxFilesToMerge;
	private static StringBuilder sb;
//	public static String mode = "ascii";
//	public static String mode = "binary";
	public static String mode;
	private static int glbPosition = 0;
//	public static String splCh = "ability.";
	private static int blockId = 0;
//	Block size
	private static int blockSize = 65536;
	private static int curBlockSize = 0;
	private static ArrayList<Byte> chunkList = new ArrayList<Byte>();
	private static ArrayList<Byte> docChunk = new ArrayList<Byte>();
	private static ArrayList<Byte> freqChunk = new ArrayList<Byte>();
	private static ArrayList<Byte> lastDocId = new ArrayList<Byte>();
	private static ArrayList<Byte> Size = new ArrayList<Byte>();
	private static ArrayList<Byte> curLastDoc = new ArrayList<Byte>();
	private static ArrayList<ChunkLexiconPartial> cLexPartial = new ArrayList<ChunkLexiconPartial>();
	private static ArrayList<Byte> ttlChunks = new ArrayList<Byte>();
	private static ArrayList<Byte> curLastDocIdSum = new ArrayList<Byte>();
	private static int ttlChunkCnt = 0;
	private static int ttlPostings = 0;
	private static int curDocIdSum = 0;
	
//	Comment later
	private static boolean matchTerm = false;
	private static int  countLastDocIdCntInBlk = 0;
	private static int blockNr;
	private static boolean isBlock = false;
	private static int prevDocIdSum = 0;
	
	private static void initialize(int max, String fileFormat) {
		maxFilesToMerge = max;
		mode = fileFormat;
	}

	
	
	// Return path of directory containing data and index files
	private static String returnPath(String pathStr) {
		URL url = Thread.currentThread().getContextClassLoader().getResource("");
		String FileName = url.getPath() + java.io.File.separator + pathStr;
		File Dir = new File(FileName);
		if (!Dir.exists()) {
			try {
				Dir.mkdir();
			} catch (Exception e) {
				System.out.println(e);
				System.out.println("Error in creating Directory " + pathStr);
				System.exit(1);
			}
		}
		return FileName;
	}
	
	private static void addChunkInBlock(ArrayList<Byte> curChunkSize) {
		chunkList.addAll(docChunk); //Add all document Ids
		chunkList.addAll(freqChunk); //Add all frequencies in existing list of chunks
		lastDocId.addAll(curLastDocIdSum); //Add last docId for current chunk
		Size.addAll(curChunkSize); //Add size of docId chunk and size of freq chunk
		curBlockSize = curBlockSize + curLastDocIdSum.size() + curChunkSize.size() + docChunk.size() + freqChunk.size();
		ttlChunkCnt++;
	}
	
	private static int addElementsInChunk(byte[] b, int j) {
		PostingNext pd = getNextId(b, j);
		curLastDoc = convertbyteToByteArray(generatePostings.getByteCode(pd.nextId));
		curDocIdSum += pd.nextId;
		docChunk.addAll(curLastDoc);
		pd = getNextId(b, pd.position); //First docId position ended one position beofre pd.position
		freqChunk.addAll(convertbyteToByteArray(generatePostings.getByteCode(pd.nextId)));
		ttlPostings++;
		return pd.position;
	}
	
	private static ArrayList<Byte> convertbyteToByteArray(byte[] b) {
		ArrayList<Byte> bArr = new ArrayList<Byte>();
		for (int i = 0; i < b.length; i++) {
			bArr.add((Byte) b[i]);
		}
		return bArr;
		
	}

//	Given a byte array convert it to integer
	private static int convertByteToNumber(ArrayList<Byte> bt) {
		int power = bt.size() - 1;
		int x = 0;
		for (Byte b :bt) {
			if (b >= 0) {
				x += b;
			} else {
				x += (Math.pow(128, power--)* (byte) (b & ~(1 << 7)));
			}
		}
		return x;
	}
	
	
	
	private static void createBlockCompress(int mergePass) {
		int numOutFiles = 0;
		int numMergePass = mergePass + 1;
//		Output Buffer to write files
		MergeBuffer mergeB = null;
//		Read Input Buffer
		partialIndexBuffer partialData = null;
		try {
//			Copy DocUrl file in new directory
			Path outDocUrlFile = Paths.get(returnPath("MergeOut_" + numMergePass).substring(1) + java.io.File.separator + "docUrl_" + numOutFiles);
			Path inDocUrlFile = Paths.get(returnPath("MergeOut_" + mergePass).substring(1) + java.io.File.separator + "docUrl_" + numOutFiles);
			Files.copy(inDocUrlFile, outDocUrlFile, StandardCopyOption.REPLACE_EXISTING);			
			if (mode.equals("ascii")) {
				mergeB = new MergeBuffer(getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "invIndexAscii_" + numOutFiles), 
						getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "lexiconAscii_" + numOutFiles), null);
				partialData = new partialIndexBuffer(
							getGzReader(new File(returnPath("MergeOut_" + mergePass) + java.io.File.separator + "invIndexAscii_" + numOutFiles)),
							getGzReader(new File(returnPath("MergeOut_" + mergePass) + java.io.File.separator + "lexiconAscii_" + numOutFiles)));
				
			} else {
				mergeB = new MergeBuffer(getBStreamWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "invIndex_" + numOutFiles), 
						getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "lexicon_" + numOutFiles), null);
				partialData = new partialIndexBuffer(
						getBStreamReader(new File(returnPath("MergeOut_" + mergePass) + java.io.File.separator + "invIndex_" + numOutFiles)),
						getGzReader(new File(returnPath("MergeOut_" + mergePass) + java.io.File.separator + "lexicon_" + numOutFiles)));
				
			}
		} catch (Exception e) {
			System.out.println(e);
			System.out.println("Error in creating compress out file");
			System.exit(1);
		}

//		Convert index into blocks of chunks of 128 postings

		try {
			while(true) {
				String nextLexStr = partialData.lexBufReader.readLine();
				String[] nextLex = null;
				int nextPos = 0;
				byte[] b = null;
				String s = null;
				if (nextLexStr != null) {
					
					nextLex = nextLexStr.trim().split("\t");
					nextPos = Integer.parseInt(nextLex[1]); //Include this index
					if (mode.equals("ascii")) {
						s = partialData.invIndBStreamAscii.readLine();
					} else {
						b = new byte[nextPos - Integer.parseInt(partialData.prevLex[1])];
						partialData.invIndBStream.read(b);
					}

				} else {
					if (mode.equals("ascii")) {
						s = partialData.invIndBStreamAscii.readLine();
					} else{
						ArrayList<Byte> ba = new ArrayList<Byte>();
						int sb;
						while((sb = partialData.invIndBStream.read()) != -1) {
							ba.add((byte)sb);
						}
						b = new byte[ba.size()];
						int bi = 0;
						for (Byte x : ba) {
							b[bi] = x.valueOf(x);
							bi++;
						}
						
					}
				}
//				Add terms in ArrayList to write it in lexicon file once chunk is collected
				int docFreq = Integer.parseInt(partialData.prevLex[2]);
				cLexPartial.add(new ChunkLexiconPartial(partialData.prevLex[0], ttlPostings, docFreq));

//				write data in chunks
				if (mode.equals("ascii")) {
//					Write ascii logic
				} else {
//					Read postings
					int j = 0;
					boolean isNewListNewChunk = false;
					if (ttlPostings < 128) {
						curDocIdSum = 0;  // If inverted list is starting from next chunk, for previous chunk last docId won't be 0
						if (isDebug) {
							prevDocIdSum = 0;
						}
	
					} else {
						isNewListNewChunk = true;
					}
					for (int i = 0; i < docFreq; i++) {
						if (ttlPostings < 128) {
							j = addElementsInChunk(b, j);

						} else {
							writeChunk(mergeB);
							if (isNewListNewChunk) {
								curDocIdSum = 0;
								if (isDebug) {
									prevDocIdSum = 0;
								}
								isNewListNewChunk = false;
							}
//							Logic to start new chunk and read current posting
//							Initialize attributes for new chunk
							initializeNewChunk();
							j = addElementsInChunk(b, j);
						}
					}
				}
				partialData.prevLex = nextLex;
				if (nextLexStr == null) {
					break;
				}
			}

//			Write remaining data
//			If after reading last inverted list, chunk size is less than 128 postings. 
//			Write that chunk into existing block if it fits or in new block
//			Need to update Lexicon as well
			
			writeChunk(mergeB);
			mergeB.bo.write(writeBlockInInvInd());

//		Close all buffers
			if (mode.equals("ascii")) {
				mergeB.boAscii.close();
				partialData.invIndBStreamAscii.close();
			} else {
				mergeB.bo.close();
				partialData.invIndBStream.close();
			}
			mergeB.bw.close();
			partialData.lexBufReader.close();
		} catch (Exception e) {
			System.out.println(e);
			e.printStackTrace();
			System.out.println("Error in reading lexbuffer or invIndBuffer");
			System.exit(1);
		}
	}

	
	public static BufferedReader getGzReader(File f) {
		try {
			InputStream fileStream = new FileInputStream(f);
			InputStream gzipStream = new GZIPInputStream(fileStream);
			Reader decoder = new InputStreamReader(gzipStream);
			return new BufferedReader(decoder);
		} catch(Exception e) {
			System.out.println("Error in creating gzip Buffered Reader");
			System.exit(1);
		}
		return null;		
	}
	
			
	private static BufferedWriter getGzWriter(String s) {
		try {
			OutputStream outStream = new FileOutputStream(s);
			OutputStream outgzipStream = new GZIPOutputStream(outStream);
			Writer outdecoder = new OutputStreamWriter(outgzipStream);
			return new BufferedWriter(outdecoder);
		} catch(Exception e) {
			System.out.println("Error in creating gzip Buffered Writer");
			System.exit(1);
		}
		return null;		
	}
	
	private static BufferedInputStream getBStreamReader(File f) {
		try {
			InputStream fileStream = new FileInputStream(f);
			return new BufferedInputStream(fileStream);
		} catch (Exception e) {
			System.out.println("Error in creating Buffered Stream Reader");
			System.exit(1);
		}
		return null;

	}
	
	private static BufferedOutputStream getBStreamWriter(String s) {
		OutputStream outStream = null;
		try {
			outStream = new FileOutputStream(s);
		} catch (FileNotFoundException e) {
			System.out.println("Error in creating Buffered Output Stream");
			System.exit(1);
		}
		return new BufferedOutputStream(outStream);
	}
		
//	Get next number from byte array and return posiiton to read number appearing after this number
	public static PostingNext getNextId(byte[] posting, int i) {
		int id;
		if (posting[i] >= 0) {
			id = posting[i];
			i++;
		} else {
			ArrayList<Byte> bt = new ArrayList<Byte>();
			while(posting[i] < 0) {
				bt.add(posting[i]);
				i++;
			}
			bt.add(posting[i]);
			i++;
			id = convertByteToNumber(bt);
		}
		return new PostingNext(id, i);
	}
	
	private static void initializeNewBlock() {
//		Increase block id
		blockId++;								
//		Initialize current block size and metadata lastDocId, size, chunkList
		curBlockSize = 0;
		ttlChunkCnt = 0;
		chunkList = new ArrayList<Byte>();
		lastDocId = new ArrayList<Byte>();
		Size = new ArrayList<Byte>();
	}
	
	private static void initializeNewChunk() {
		ttlPostings = 0;
		docChunk = new ArrayList<Byte>();
		freqChunk = new ArrayList<Byte>();
	}
	
	// list data files from given directory
	private static File[] listFiles(String dirName) {
		File dir = new File(dirName);
		// Filter to select only data files
		FilenameFilter fileNameFilter = new FilenameFilter() {
			@Override
			public boolean accept(File dir, String name) {
				if (mode.equals("ascii")) {
					if (name.startsWith("invIndexAscii_")) {
						return true;
					}
				} else {
					if (name.startsWith("invIndex_")) {
						return true;
					}
				}
				return false;
			}
		};
		return dir.listFiles(fileNameFilter);
	}
	
//	Return next record to be entered in MinHeap.
	private static HeapStruct nextRecord(int i, ArrayList<partialIndexBuffer> partialData) {
		partialIndexBuffer ib = partialData.get(i);
		if (ib.prevLex == null) {
			return null;
		}
		HeapStruct t = null;
		try {
			String nextLexStr = ib.lexBufReader.readLine();
			String[] nextLex = null;
			int nextPos = 0;
			byte[] b = null;
			String s = null;
			
			if (nextLexStr != null) {
				
				nextLex = nextLexStr.trim().split("\t");
				nextPos = Integer.parseInt(nextLex[1]); //Include this index
				if (mode.equals("ascii")) {
					s = ib.invIndBStreamAscii.readLine();
				} else {
					b = new byte[nextPos - Integer.parseInt(ib.prevLex[1])];
					ib.invIndBStream.read(b);
				}

			} else {
				if (mode.equals("ascii")) {
					s = ib.invIndBStreamAscii.readLine();
				} else{
					ArrayList<Byte> ba = new ArrayList<Byte>();
					int sb;
					while((sb = ib.invIndBStream.read()) != -1) {
						ba.add((byte)sb);
					}
					b = new byte[ba.size()];
					int bi = 0;
					for (Byte x : ba) {
						b[bi] = x.valueOf(x);
						bi++;
					}
				}

			}

			if (mode.equals("ascii")) {
				t = new HeapStruct(ib.prevLex[0], i, Integer.parseInt(ib.prevLex[2]), Integer.parseInt(ib.prevLex[1]), s);
			} else {
				t = new HeapStruct(ib.prevLex[0], i, Integer.parseInt(ib.prevLex[2]), Integer.parseInt(ib.prevLex[1]), b);
			}

			ib.prevLex = nextLex;

		} catch (Exception e) {
			System.out.println(e);
			e.printStackTrace();
			System.out.println("Error in reading lexbuffer or invIndBuffer");
			System.exit(1);
		}
		return t;
		
		
	}
	
//	Read index data files from given list and merge them to subindex as per maxFilesToMerge size till there is only one
//	set of files left(Inverted Index, Lexicon and Page table)
	private static void readInvIndexFiles(File[] listF) {
		int numMergePass = 0;
		int maxDegree = maxFilesToMerge;
		int numOutFiles = 0;
		while (numOutFiles != 1) {
			if (numOutFiles == 0 && numMergePass > 0) {
				break;
			}
			File[] listOfFiles;
			numOutFiles = 0;
			int ttlReadFiles = 0;
			if (numMergePass == 0) {
				listOfFiles = listF;
			} else {
				int mo = numMergePass - 1;
				listOfFiles = listFiles(returnPath("MergeOut_" + mo));
			}
			System.out.println("Pass number is " + numMergePass);
			while(ttlReadFiles < listOfFiles.length) {
				
				sb = new StringBuilder();
//				Output Buffer to write files
				MergeBuffer mergeB = null;
//				Read Input Buffer
				ArrayList<partialIndexBuffer> partialData = new ArrayList<partialIndexBuffer>();
				int docIdStart = 0;
				fileDocMap = new HashMap<Integer, Integer>();
				try {
					if (mode.equals("ascii")) {
						mergeB = new MergeBuffer(getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "invIndexAscii_" + numOutFiles), 
								getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "lexiconAscii_" + numOutFiles), 
								getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "docUrl_" + numOutFiles));
					} else {
						mergeB = new MergeBuffer(
								getBStreamWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "invIndex_" + numOutFiles), 
								getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "lexicon_" + numOutFiles), 
								getGzWriter(returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "docUrl_" + numOutFiles));
						
					}
				} catch (Exception e) {
					System.out.println(e);
					System.out.println("Error in creating mergeout files " + numOutFiles + " for Merge Pass " + numMergePass );
					System.exit(1);
				}

				int degree = 0;
				for (degree = 0; degree < maxDegree; degree++) {
					try {
						if (ttlReadFiles >= listOfFiles.length) {
							break;
						}
//						Get lexicon structure file name for corresponding inverted index file name
						String parentPath = listOfFiles[ttlReadFiles].getParent();
						String invIndFileNm = listOfFiles[ttlReadFiles].getName();
						System.out.println(" Processing files " + invIndFileNm); 
						String cnt = invIndFileNm.substring(invIndFileNm.indexOf('_') + 1);
						//Write DocUrl File
						fileDocMap.put(degree, docIdStart);
						docIdStart = writeDocUrlFile(getGzReader(new File(parentPath + java.io.File.separator + "docUrl_" + cnt)), 
									docIdStart, mergeB.docUrlbw);
						if (mode.equals("ascii")) {
							partialData.add(new partialIndexBuffer(getGzReader(listOfFiles[ttlReadFiles]), 
									getGzReader(new File(parentPath + java.io.File.separator + "lexiconAscii_" + cnt))));
						} else {
							partialData.add(new partialIndexBuffer(getBStreamReader(listOfFiles[ttlReadFiles]), 
											getGzReader(new File(parentPath + java.io.File.separator + "lexicon_" + cnt))));
						}

					} catch (Exception e) {
						System.out.println(e);
						System.out.println("Error in reading file " + listOfFiles[ttlReadFiles]);
						System.exit(1);
					}
					ttlReadFiles++;
				}
				if (degree == 0) {
					break;
				}
				MinHeap heap = new MinHeap(degree);
				
				for (int i = 0; i < degree; i++) {
					HeapStruct nxtR = nextRecord(i, partialData);
//					System.out.println(nxtR.toString());
					if (nxtR == null) {
						//Reduce size of heap
						heap.delete();
					} else {
						heap.insert(nxtR);
					}
				}
//				Merge files
				while (heap.getSize() > 0) {
//					Write minimum record to output
					HeapStruct front= heap.getFront();
//					Uncomment Later
					writeRecord(front, mergeB);
//					replace minumum in heap by next record in that file
					HeapStruct nxtR = nextRecord(front.fileNr, partialData);
					if (nxtR == null) {
						heap.delete();
					} else {
						heap.replaceFront(nxtR);
					}

				}
//				To write last record
				writeRecord(null, mergeB);
			
//				Write records in file. Can include in writeRecord method
				for (int i = 0; i < degree; i++) {
					try {
						if (mode.equals("ascii")) {
							partialData.get(i).invIndBStreamAscii.close();
						} else {
							partialData.get(i).invIndBStream.close();
						}
						partialData.get(i).lexBufReader.close();
					} catch (Exception e) {
						System.out.println(e);
						System.out.println("Error in closing partial inv index files");
						System.exit(1);
					}
				}
				
				try {
					if (mode.equals("ascii")) {
						mergeB.boAscii.close();
						glbPosition = 0;
					} else {
						mergeB.bo.close();
					}
					mergeB.bw.close();
					mergeB.docUrlbw.close();
				} catch (Exception e) {
					System.out.println(e);
					System.out.println("Error in closing out merge file");
					System.exit(1);
				}

				numOutFiles++;
			}
			numMergePass++;
		}
//		System.out.println(numMergePass);
		createBlockCompress(numMergePass - 1);

	}
	
	

//	For binary files update doc ID in posting according to merge file Page table numbers.
	private static byte[] updateDocIdPosting(HeapStruct data, MergeBuffer mergeB) {
		int i = 0;
		int docId, docFreq, newDocId = 0;
		int lastPos = 0;
		int sumDocId = 0;
		int docIdStart = 0;
		int prevDocId = mergeB.prevDocId;
		byte[] tempBytes = null;
		ArrayList<Byte> ba = new ArrayList<Byte>();
//		System.out.println("Doc freq is " + data.docFreq);
		for (int j = 0; j < data.docFreq; j++) {
			PostingNext pd = getNextId(data.posting, i);
			docId = pd.nextId;
			sumDocId += docId;
			int docIdPos = pd.position; //First docId position ended one position beofre it
//			Comment Remove try and catch block
			try {
				pd = getNextId(data.posting, pd.position);
			} catch (Exception e) {
				System.out.println("Exception " + e);
			}

			docFreq = pd.nextId;
			i = pd.position;
			if (j == 0) {
				lastPos = docIdPos;
				docIdStart = fileDocMap.get(data.fileNr);
				newDocId = docId + docIdStart;
				tempBytes = generatePostings.getByteCode(newDocId - prevDocId);
			}
		}
		byte[] finalB = new byte[tempBytes.length + data.posting.length - lastPos];
		System.arraycopy(tempBytes, 0, finalB, 0, tempBytes.length);
		System.arraycopy(data.posting, lastPos, finalB, tempBytes.length, data.posting.length - lastPos);
		mergeB.prevDocId = sumDocId + docIdStart;
		return finalB;
		
		
	}

	private static String updateDocIdPostingAscii(HeapStruct data, MergeBuffer mergeB) {
		int docId, docFreq, newDocId = 0;
		int lastPos = 0;
		int sumDocId = 0;
		int docIdStart = 0;
		int prevDocId = mergeB.prevDocId;
		String[] s = null;
		try {
			s = data.postingAscii.split(",");
		} catch (Exception e) {
			System.out.println("Exception " + e);
		}
		
		docIdStart = fileDocMap.get(data.fileNr);
		StringBuilder rs = new StringBuilder();
		for (int i = 0; i < s.length; i++) {
			String[] p = s[i].split(":");
			sumDocId += Integer.parseInt(p[0]);
			if (i == 0) {
				newDocId = Integer.parseInt(p[0]) + docIdStart;
				s[i] = newDocId  + ":" + p[1];
			}
			rs.append(s[i] + ",");
		}

		mergeB.prevDocId = sumDocId + docIdStart;
		return rs.toString();
	}
	
	private static void updateLexicon(MergeBuffer mergeB) {
//		for (ChunkLexiconPartial elem : cLexPartial) {
		if (cLexPartial.size() == 0) {
			return;
		}
		int len = cLexPartial.size();
		boolean skipLast = (cLexPartial.get(cLexPartial.size() - 1).postingNr == 128);
		if (skipLast) {
			len = cLexPartial.size() - 1;
		}
		for (int i = 0; i < len; i++) {
			ChunkLexiconPartial elem = cLexPartial.get(i);
			try {
				mergeB.bw.write(elem.term + "\t" + blockId + "\t" + ttlChunkCnt + "\t" + elem.postingNr + "\t" + elem.docFreq + "\n");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				System.out.println("Error in updating lexicon");
				System.exit(1);
			}
		}
		if (skipLast) {
			ChunkLexiconPartial partial = cLexPartial.get(cLexPartial.size() - 1);
			partial.postingNr = 0;
			cLexPartial = new ArrayList<ChunkLexiconPartial>();
			cLexPartial.add(partial);
		} else {
			cLexPartial = new ArrayList<ChunkLexiconPartial>();
		}

	}
	
	private static byte[] writeBlockInInvInd() {
//		Comment later
		isBlock = false;
		if (blockNr == 679) {
			isBlock = true;
		}
		ttlChunks = convertbyteToByteArray(generatePostings.getByteCode(ttlChunkCnt));
		if (matchTerm) {
			System.out.println("Total Chunk Count is " + ttlChunkCnt);
			System.out.println("LastId Count added " + countLastDocIdCntInBlk + " times");
		}
//		Logic if block can not accomodate these 128 postings
//		Pad remaining bytes of block with 0
		byte[] blockBytes = new byte[blockSize];
		int k = 0;
		int listSize = 0;
		while (listSize < ttlChunks.size()) {
			blockBytes[k++] = ttlChunks.get(listSize++);
		}
		listSize = 0;
		if (matchTerm) {
			System.out.println("Position after reading total chunks size " + k);
			System.out.println("Last Doc Id Array ");
		}
		while (listSize < lastDocId.size()) {
			blockBytes[k++] = lastDocId.get(listSize++);
			if (matchTerm) {
				System.out.print(lastDocId.get(listSize - 1) + " , ");
			}
		}
		listSize = 0;
		if (matchTerm) {
			System.out.println();
			System.out.println("Last docId in int ");
			int q = 0;
			byte[] bLastDoc = new byte[lastDocId.size()];
			for (int r = 0; r < lastDocId.size(); r++) {
				bLastDoc[r] = lastDocId.get(r);
			}
			System.out.println("Last DocId in int form");
			while ( q < lastDocId.size()) {
				PostingNext qTestObj = generateIndex.getNextId(bLastDoc, q);
				q = qTestObj.position;
				System.out.print(qTestObj.nextId + " , ");
			}
			System.out.println();
			System.out.println("Size of last doc id " + lastDocId.size());
			System.out.println("value of k is " + k);
		}
		while (listSize < Size.size()) {
			blockBytes[k++] = Size.get(listSize++);
		}
//		Comment later
		if (matchTerm) {
			System.out.println();
		}
		listSize = 0;
		while (listSize < chunkList.size()) {
			blockBytes[k++] = chunkList.get(listSize++);
		}
		blockNr++;
		return blockBytes;
	}
	
	private static void writeChunk(MergeBuffer mergeB) {
//		If ttlPosting is equal to 128, then write all postings in chunk and update block metadata
		ArrayList<Byte> curChunkSize = new ArrayList<Byte>();
		curChunkSize.addAll(convertbyteToByteArray(generatePostings.getByteCode(docChunk.size())));
		curChunkSize.addAll(convertbyteToByteArray(generatePostings.getByteCode(freqChunk.size())));
//		curBlocksize doesn't include ttl Number of chunks in block size
		ttlChunks = convertbyteToByteArray(generatePostings.getByteCode(ttlChunkCnt + 1));
		curLastDocIdSum = convertbyteToByteArray(generatePostings.getByteCode(curDocIdSum));
		if (curBlockSize + ttlChunks.size() + curLastDocIdSum.size() + curChunkSize.size() + docChunk.size() + freqChunk.size() 
				<= blockSize) {
			addChunkInBlock(curChunkSize);
//			Add terms in Lexicon and initialize cLexPartial
			updateLexicon(mergeB);
			
			
		} else {
//			Write current block in inverted index file
			try {
				if (matchTerm) {
					System.out.println("Actual size " + (curBlockSize + ttlChunks.size()));
					int k = 0;
					int sum = 0;
					int i = 0;
					byte[] sizeByte = new byte[Size.size()];
					for (byte b : Size) {
						sizeByte[i] = Size.get(i);
						i++;
					}
					while (k < Size.size()) {
						PostingNext tempObj = generateIndex.getNextId(sizeByte, k);
						sum += tempObj.nextId;
						k = tempObj.position;
					}
					if (sum > 65536) {
						System.out.println("Error");
						System.out.println("Sum of Chunk size " + sum);
						System.exit(1);
					}
					System.out.println("Sum of Chunk size " + sum);
					System.out.println("Extra Size " + (curBlockSize + ttlChunks.size() + curLastDocIdSum.size() + curChunkSize.size() + docChunk.size() + freqChunk.size()));
				}
				mergeB.bo.write(writeBlockInInvInd());
				matchTerm = false;
			} catch (IOException e) {
				// TODO Auto-generated catch block
				System.out.println("Error in writing block");
				System.exit(1);
			}
			initializeNewBlock();
//			Write chunk in new Block
			addChunkInBlock(curChunkSize);
//			Add terms in Lexicon and initialize lexTerms and chunkPostingNr
			updateLexicon(mergeB);								
			
		}
	}
	
	private static int writeDocUrlFile(BufferedReader docUrlFile, int docIdStart, BufferedWriter docUrlBw) {
		String line = null;
		int id = 0;
		try {
			while ((line = docUrlFile.readLine()) != null) {
				String[] s = line.trim().split("\t", 2);
				id = docIdStart + Integer.parseInt(s[0]);
				docUrlBw.write(id + "\t" + s[1] + "\n");
			}
			return id;
		} catch (Exception e) {
			System.out.println(e);
			System.out.println("Error in reading docUrl file");
			System.exit(1);
		}
		return id;

	}
	
	private static void writeRecord(HeapStruct data, MergeBuffer mergeB) {
		if (data != null) {
			if (mergeB.prevTerm == null) {
				mergeB.prevTerm = data.term;
				mergeB.prevDocFreq = data.docFreq;
				mergeB.prevDocId = 0;
				if (mode.equals("ascii")) {
					mergeB.prevInvAscii = updateDocIdPostingAscii(data, mergeB);
				} else {
					mergeB.prevInv = updateDocIdPosting(data, mergeB);
				}
			} else {
				if (data.term.equals(mergeB.prevTerm)) {
					mergeB.prevDocFreq += data.docFreq;
					if (mode.equals("ascii")) {
						String s = updateDocIdPostingAscii(data, mergeB);
						StringBuilder st = new StringBuilder();
						st.append(mergeB.prevInvAscii);
						st.append(s);
						mergeB.prevInvAscii = st.toString();
					} else {
						byte[] updPosting = updateDocIdPosting(data, mergeB);
						byte[] newUpd = new byte[mergeB.prevInv.length + updPosting.length];
						System.arraycopy(mergeB.prevInv, 0, newUpd, 0, mergeB.prevInv.length);
						System.arraycopy(updPosting, 0, newUpd, mergeB.prevInv.length, updPosting.length);
						mergeB.prevInv = newUpd; 
					}

//					Merge two terms
				} else {
					try {
//						write prev term to buffer
						String s = mergeB.prevTerm + "\t" + mergeB.glbPosition + "\t" + mergeB.prevDocFreq + "\n";
						mergeB.bw.write(s);
//						Update docIds
						if (mode.equals("ascii")) {
							mergeB.boAscii.write(mergeB.prevInvAscii + "\n"); 
						} else {
							mergeB.bo.write(mergeB.prevInv); 
						}

					} catch (Exception e) {
						System.out.println(e);
						System.out.println("Error in writing merge file");
						System.exit(1);
					}
//					Make current term as previous term
					mergeB.prevTerm = data.term;
					mergeB.prevDocFreq = data.docFreq;
					mergeB.prevDocId = 0;
					if (mode.equals("ascii")) {
//						Update glbPosition
						mergeB.glbPosition += 1;
						mergeB.prevInvAscii = updateDocIdPostingAscii(data, mergeB);
					} else {
//						Update glbPosition
						mergeB.glbPosition += mergeB.prevInv.length;
						mergeB.prevInv = updateDocIdPosting(data, mergeB);
					}
				}
			}
		} else {
//			write prev record directly
			try {
//				write prev term to buffer
				mergeB.bw.write(mergeB.prevTerm + "\t" + mergeB.glbPosition + "\t" + mergeB.prevDocFreq + "\n");
//				Update docIds
				if (mode.equals("ascii")) {
					mergeB.boAscii.write(mergeB.prevInvAscii + "\n");
				} else {
					mergeB.bo.write(mergeB.prevInv); 
				}
			} catch (Exception e) {
				System.out.println(e);
				System.out.println("Error in writing merge file");
				System.exit(1);
			}
		}
		
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		System.out.println("Start Time " + Calendar.getInstance().getTime());
		int maxFilestoMerge = 100;
		String fileFormat = "binary";
		initialize(maxFilestoMerge, fileFormat);
		readInvIndexFiles(listFiles(returnPath("PostingOutput")));
		//Convert final index to compress format..Convert intermediate index to compress format later if time permits
		
		System.out.println("End Time " + Calendar.getInstance().getTime());
		

		
		
		
		

		
	}
}

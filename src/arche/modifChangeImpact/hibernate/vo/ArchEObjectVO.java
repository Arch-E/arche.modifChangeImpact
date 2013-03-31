/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact.hibernate.vo;

/**
 * Main VO class for the implementation of 'versionable' ArchE concepts.  
 * 
 * @author Andres Diaz-Pace
 */

import edu.cmu.sei.arche.external.data.ArchEObject;
import edu.cmu.sei.arche.external.data.ArchEVersion;

public class ArchEObjectVO implements ArchEObject, java.io.Serializable {
	
	private static final long serialVersionUID = 1L;

	private static final String DEFAULT_ARCHE_SOURCE = "ArchE";
	
	protected int versionNumber;
	protected String factId;
	protected ArchEVersionVO version;
	protected String source;
	
	public ArchEObjectVO() {
		this(null);		
	}

	public ArchEObjectVO(ArchEVersion version) {
		if (version != null) {
			this.version = (ArchEVersionVO)(version);
			versionNumber = version.getId();			
			factId = version.generateUniqueFactID();
		}
		else  {
			version = null;
			versionNumber = -1;
			factId = "<Fact-0>";			
		}
		source = DEFAULT_ARCHE_SOURCE;
	}
	
	public String getName() {
		return (this.getClass().getName());
	}

	public void setSource(String s) {
		source = s;
	}
	
	public String getSource() {
		return (source);
	}
	
	public int getVersionNumber() {
		return this.versionNumber;
	}

	public void setVersionNumber(int versionNumber) {
		this.versionNumber = versionNumber;
	}

	public String getFactId() {
		return this.factId;
	}

	public void setFactId(String factId) {
		this.factId = factId;
	}

	public ArchEVersionVO getVersion() {
		return this.version;
	}

	public void setVersion(ArchEVersionVO version) {
		this.version = version;
		this.versionNumber = version.getId();
	}

}

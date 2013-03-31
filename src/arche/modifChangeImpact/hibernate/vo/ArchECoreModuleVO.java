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
 * VO class that represents a module in the module viewtype.
 * <p>
 * This core design concept can be specialized for user-specific needs
 * 
 * @author Andres Diaz-Pace
 */

import edu.cmu.sei.arche.external.data.ArchEDesignElement;
import edu.cmu.sei.arche.external.data.ArchEVersion;

public class ArchECoreModuleVO extends ArchEObjectVO implements ArchEDesignElement, 
													java.io.Serializable {

	private static final long serialVersionUID = 1L;
	
	private Integer uid;
	private String name;
	private int status;
	private String id; // TODO: To be removed (it's not defined in the DB schema)

//	// Specific properties of the module
//	private double costOfChange;
//	private double complexity;
//
	public ArchECoreModuleVO() {
		super();		
//		costOfChange = 0.0;
//		complexity = 0.0;
	}
	
	public ArchECoreModuleVO(ArchEVersion version) {
		super(version);
//		costOfChange = 0.0;
//		complexity = 0.0;
	}

	public Integer getUid() {
		return this.uid;
	}

	public void setUid(Integer uid) {
		this.uid = uid;
	}

	public String getName() {
		return this.name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public int getStatus() {
		return this.status;
	}

	public void setStatus(Integer status) {
		this.status = status;
	}

	public String getId() {
		return this.id;
	}

	public void setId(String id) {
		this.id = id;
	}

	// Note: We need to consider several cases of comparison. 
	public boolean equals(Object anotherModule) {

		// 0) if anotherModule == null
		if (anotherModule == null)
			return (false);
		
		if (anotherModule instanceof ArchECoreModuleVO) {		
			// 1) comparison for VO objects generated from DB which have their Uids.
			Integer moduleUid = ((ArchECoreModuleVO)anotherModule).getUid();
			if ((moduleUid != null) && (uid != null))
				//return (moduleUid.intValue() == uid.intValue());
				if (moduleUid.intValue() == uid.intValue())
					return (true);
				else if (anotherModule != null) {
					if (((ArchECoreModuleVO)anotherModule).getName().equals(name))
						return (true);		
					// TODO: The comparison could alternatively use getFactId(), although it would
					// expose Jess implementation details to the RF developer
				}
		
		}

		// 2) comparison for VO objects created outside of Hibernate which have no uid.
		return (this == anotherModule);
	}

}


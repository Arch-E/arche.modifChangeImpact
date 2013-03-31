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
 * VO class that represents an ArchE responsibility
 * <p>
 * A responsibility can have several parameters associated to it. A parameter is
 * a pair <name, value>. Allowed value types for parameters are integer, double, 
 * string or boolean.
 * <p>
 * Responsibilities are usually part of a responsibility structure. We assume a 
 * reasoning framework can create/manipulate responsibilities, but it cannot delete 
 * existing responsibilities (this is performed only by the ArchE core)
 * <p>
 * This is a core concept that should not be extended by reasoning frameworks
 * 
 * @author Hyunwoo Kim, Andres Diaz-Pace
 */

import java.util.Hashtable;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEVersion;

public class ArchEResponsibilityVO extends ArchEObjectVO implements ArchEResponsibility {

	private static final long serialVersionUID = 1L;
	
	private Integer uid;
	private String id;
	private String name;
	private String description;
	private int status;

	// The container for this responsibility
	private ArchEResponsibilityStructureVO responsibilityStructure;
	
	// For parameters of the form <name,value>
	private Hashtable<String,Object> myParameters = null; // 

	public ArchEResponsibilityVO() {
		super();
		myParameters = new Hashtable<String,Object> ();
	}
	
	public ArchEResponsibilityVO(ArchEVersion version) {
		super(version);
		myParameters = new Hashtable<String,Object> ();
	}

	public Integer getUid() {
		return this.uid;
	}

	public void setUid(Integer uid) {
		this.uid = uid;
	}

	public ArchEResponsibilityStructureVO getResponsibilityStructure() {
		return this.responsibilityStructure;
	}

	public void setResponsibilityStructure(
			ArchEResponsibilityStructureVO responsibilityStructure) {
		this.responsibilityStructure = responsibilityStructure;
	}

	public String getId() {
		return this.id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public String getName() {
		return this.name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getDescription() {
		return this.description;
	}

	public void setDescription(String description) {
		this.description = description;
	}

	public int getStatus() {
		return this.status;
	}

	public void setStatus(int status) {
		this.status = status;
	}

	public boolean equals(Object anotherResponsibility) {
		
		if (anotherResponsibility == null)
			return (false);
		
		if (anotherResponsibility instanceof ArchEResponsibilityVO) {
			Integer responsibilityUid = ((ArchEResponsibilityVO)anotherResponsibility).getUid();
			if ((responsibilityUid != null) && (uid != null)) {
				//return (responsibilityUid.intValue() == uid.intValue());
				if (responsibilityUid.intValue() == uid.intValue())
					return (true);				
				else if (anotherResponsibility != null) {
					if (((ArchEResponsibilityVO)anotherResponsibility).getName().equals(name))
						return (true);
					// TODO: The comparison could alternatively use getFactId(), although it would
					// expose Jess implementation details to the RF developer
				}
			}
			
		}		
		
		return (this == anotherResponsibility);
	}
	
	//---- Methods for manipulation of parameters ----
	
	public String getStringParameter(String propertyName) throws ArchEException {
		Object value = myParameters.get(propertyName);
		if ((value != null) && (value instanceof String))
			return ((String)value);
		else
			throw new ArchEException("No parameter[string]: "+propertyName+" available in responsibility: "+this.getName());
	}
	
	public boolean getBooleanParameter(String parameterName)throws ArchEException  {
		Object value = myParameters.get(parameterName);
		if ((value != null) && (value instanceof Boolean))
			return ((Boolean)value);
		else
			throw new ArchEException("No parameter[boolean]: "+parameterName+" available in responsibility: "+this.getName());
	}
	
	public double getDoubleParameter(String parameterName) throws ArchEException {
		Object value = myParameters.get(parameterName);
		if ((value != null) && (value instanceof Double))
			return ((Double)value);
		else
			throw new ArchEException("No parameter[double]: "+parameterName+" available in responsibility: "+this.getName());
	}

	public int getIntegerParameter(String parameterName) throws ArchEException {
		Object value = myParameters.get(parameterName);
		if ((value != null) && (value instanceof Integer))
			return ((Integer)value);
		else
			throw new ArchEException("No parameter[integer]: "+parameterName+" available in responsibility: "+this.getName());
	}

	public boolean hasParameter(String parameterName) {
		return (myParameters.containsKey(parameterName));
	}
	
	public void defineParameter(String parameterName, Object value) {
		// This method should only be invoked by the appropriate subclass of 
		// ArchECoreResponsibilityStructure or by the reasoning framework class
		myParameters.put(parameterName, value);
		return;
	}

}
